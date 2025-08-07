{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Chan.Mux (
  ToFromBundleMsg (..),
  ConnectionBundle (..),
  mapBearerTracer,
  newMuxChan,
) where

import Chan.Core (Chan (..))
import Chan.TCP (Bytes, MessageSize (..))
import qualified Control.Category as Cat
import Control.Concurrent.Class.MonadMVar (MonadMVar (..))
import qualified Control.Lens as Lens
import Control.Monad (forM_, forever)
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Control.Tracer (Tracer (Tracer), traceWith)
import Data.Array (Array, listArray, (!))
import Data.Kind
import Data.Foldable (traverse_)
import Data.Functor.Const (Const (Const), getConst)
import STMCompat

class ConnectionBundle bundle where
  type BundleMsg bundle
  type BundleConstraint bundle :: Type -> Constraint
  toFromBundleMsgBundle :: bundle (ToFromBundleMsg (BundleMsg bundle))
  traverseConnectionBundle :: Monad m => (forall a. BundleConstraint bundle a => f a -> m (g a)) -> bundle f -> m (bundle g)

-- | Injection, projection, between a common mux message type, and an
-- individual message type. The following must hold:
--
-- > fromBundleMsg (toBundleMsg x) = x
--
-- But 'fromBundleMsg' is not required to be defined outside of the image of
-- 'toBundleMsg'. For example, a valid implementation would be:
--
-- > ToFromBundleMsg toDynamic (fromJust . fromDynamic)
data ToFromBundleMsg mm a
  = ToFromBundleMsg
  { toBundleMsg :: a -> mm
  , fromBundleMsg :: mm -> a
  }

instance Cat.Category ToFromBundleMsg where
  id = ToFromBundleMsg id id
  (.) (ToFromBundleMsg f f') (ToFromBundleMsg g g') = ToFromBundleMsg (g . f) (f' . g')

-- dynToFromBundleMsg :: Typeable a => ToFromBundleMsg Dynamic a
-- dynToFromBundleMsg = ToFromBundleMsg toDyn (fromJust . fromDynamic)

data BorneMsg a = BorneMsg !Int a

-- | Each bearer message is some slices of various 'BorneMsg's
--
-- The mini protocols never see this, so this type is not exported. It does
-- occur in the argument types of some exported functions, but the caller
-- should be using parametric functions to generate those arguments.
data BearerMsg a = BearerMsg !Bytes [BorneMsg a]
  -- ^ the cumulative size of the slices the borne messages whose /final/ slice
  -- is in this message

instance MessageSize (BearerMsg a) where
  messageSizeBytes (BearerMsg sz _) = 1 + sz

mapBearerTracer ::
  Applicative m =>
  Lens.Lens s t (BearerMsg a) a ->
  Tracer m t ->
  Tracer m s
mapBearerTracer lens tracer = Tracer $ \x -> do
  let BearerMsg _ msgs = getConst $ lens Const x -- why doesn't Lens.view lens x type check?
  flip traverse_ msgs $ \(BorneMsg _ a) -> do
    traceWith tracer $ Lens.set lens a x

newMuxChan ::
  forall bundle m.
  (ConnectionBundle bundle, MonadMVar m, MonadSTM m, MonadFork m, MessageSize (BundleMsg bundle)) =>
  Chan m (BearerMsg (BundleMsg bundle)) ->
  m (bundle (Chan m))
newMuxChan bearer = do
  -- Bit of a hack to use these TVars, could run the traverseConnectionBundle
  -- in a reader+state monad instead. That'd be cleaner.
  recvQueuesAccum <- newTVarIO []
  recvQueuesIx <- newTVarIO (0 :: Int)
  sendQueue <- newTQueueIO
  chans <-
    traverseConnectionBundle
      ( newMuxChanSingle @bundle
          sendQueue
          recvQueuesIx
          recvQueuesAccum
      )
      toFromBundleMsgBundle
  recvQueues <- reverse <$> readTVarIO recvQueuesAccum
  let recvQueues' = listArray (0, length recvQueues - 1) recvQueues
  _ <- forkIO $ demuxer @bundle bearer recvQueues'
  _ <- forkIO $ muxer @bundle bearer sendQueue
  return chans

newMuxChanSingle ::
  forall bundle m a.
  (MonadMVar m, MonadSTM m, MessageSize (BundleMsg bundle)) =>
  TQueue m (MVar m (), Bytes, BorneMsg (BundleMsg bundle)) ->
  TVar m Int ->
  TVar m [RecvQueue m (BundleMsg bundle)] ->
  ToFromBundleMsg (BundleMsg bundle) a ->
  m (Chan m a)
newMuxChanSingle
  sendQueue
  recvQueuesIx
  recvQueuesAccum
  ToFromBundleMsg{..} = do
    recvQueue <- newTQueueIO
    -- A mini protocol can have at most one message in the send buffer.
    sendLock <- newMVar ()
    i <- atomically $ do
      modifyTVar recvQueuesAccum (RecvQueue fromBundleMsg recvQueue :)
      i <- readTVar recvQueuesIx
      writeTVar recvQueuesIx $! (i + 1)
      return i
    return
      Chan
        { readChan = atomically (readTQueue recvQueue)
        , writeChan = \msg -> do
            let !bundleMsg = toBundleMsg msg
                !muxmsg = BorneMsg i bundleMsg
            takeMVar sendLock
            atomically $
              writeTQueue sendQueue $
              (sendLock, messageSizeBytes bundleMsg, muxmsg)
        }

data RecvQueue m mm where
  RecvQueue :: (mm -> a) -> TQueue m a -> RecvQueue m mm

demuxer ::
  forall bundle m.
  MonadSTM m =>
  Chan m (BearerMsg (BundleMsg bundle)) ->
  Array Int (RecvQueue m (BundleMsg bundle)) ->
  m ()
demuxer bearer queues =
  forever $ do
    BearerMsg _ msgs <- readChan bearer
    forM_ msgs $ \(BorneMsg i msg) ->
      case queues ! i of
        RecvQueue convert queue ->
          atomically $ writeTQueue queue $! convert msg

muxer ::
  forall bundle m.
  (MonadMVar m, MonadSTM m) =>
  Chan m (BearerMsg (BundleMsg bundle)) ->
  TQueue m (MVar m (), Bytes, BorneMsg (BundleMsg bundle)) ->
  m ()
muxer bearer sendQueue =
    forever $ do
      x <- atomically (readTQueue sendQueue)
      (muxmsg, locks) <- go 0 [] [] x
      mapM_ (flip putMVar ()) locks
      writeChan bearer muxmsg
  where
    --- from ouroboros-network's @Network.Mux.Bearer.makeSocketBearer'@
    sliceBytes = 12288
    loafBytes = 131072

    go !accBytes acc locks (lock, bytes, msg) = do
      let !accBytes' = accBytes + min sliceBytes bytes
      (acc', locks') <-
        if bytes <= sliceBytes
        then do
          -- We do not release the lock before finalizing the loaf because a
          -- single loaf should include slices from at most one borne message
          -- per protocol.
          pure (msg : acc, lock : locks)
        else do
          -- reenqueue the rest of the message
          let !bytes' = bytes - sliceBytes
          atomically $ writeTQueue sendQueue (lock, bytes', msg)
          pure (acc, locks)

      let result = (BearerMsg accBytes' acc', locks')
      if accBytes' >= loafBytes then pure result else do
        atomically (tryReadTQueue sendQueue) >>= \case
          Nothing -> pure result
          Just x -> go accBytes' acc' locks' x

data ExampleBundle f = ExampleBundle
  { exampleFoo :: f Int
  , exampleBar :: f Bool
  }

data ExampleMsg
  = MsgFoo {fromMsgFoo :: Int}
  | MsgBar {fromMsgBar :: Bool}

-- TODO: No other way to define an always true constraint that can be
-- partially applied?
class NoConstraint a
instance NoConstraint a

instance ConnectionBundle ExampleBundle where
  type BundleMsg ExampleBundle = ExampleMsg
  type BundleConstraint ExampleBundle = NoConstraint

  toFromBundleMsgBundle =
    ExampleBundle
      { exampleFoo = ToFromBundleMsg MsgFoo fromMsgFoo
      , exampleBar = ToFromBundleMsg MsgBar fromMsgBar
      }

  traverseConnectionBundle f ExampleBundle{..} =
    ExampleBundle
      <$> f exampleFoo
      <*> f exampleBar
