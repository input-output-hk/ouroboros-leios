{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Chan.Mux (
  ToFromBundleMsg (..),
  ConnectionBundle (..),
  fromBearerMsg,
  newMuxChan,
) where

import Chan.Core (Chan (..))
import Chan.TCP (MessageSize (..))
import qualified Control.Category as Cat
import Control.Concurrent.Class.MonadMVar (MonadMVar (..))
import Control.Monad (forever)
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Data.Array (Array, listArray, (!))
import STMCompat

class ConnectionBundle bundle where
  type BundleMsg bundle
  toFromBundleMsgBundle :: bundle (ToFromBundleMsg (BundleMsg bundle))
  traverseConnectionBundle :: Monad m => (forall a. f a -> m (g a)) -> bundle f -> m (bundle g)

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

data BearerMsg a = BearerMsg !Int a

fromBearerMsg :: BearerMsg a -> a
fromBearerMsg (BearerMsg _ a) = a

instance MessageSize a => MessageSize (BearerMsg a) where
  messageSizeBytes (BearerMsg _ a) = 1 + messageSizeBytes a

newMuxChan ::
  forall bundle m.
  (ConnectionBundle bundle, MonadMVar m, MonadSTM m, MonadFork m) =>
  Chan m (BearerMsg (BundleMsg bundle)) ->
  m (bundle (Chan m))
newMuxChan bearer = do
  sendLock <- newMVar ()
  -- Bit of a hack to use these TVars, could run the traverseConnectionBundle
  -- in a reader+state monad instead. That'd be cleaner.
  recvQueuesAccum <- newTVarIO []
  recvQueuesIx <- newTVarIO 0
  chans <-
    traverseConnectionBundle
      ( newMuxChanSingle @bundle
          bearer
          sendLock
          recvQueuesIx
          recvQueuesAccum
      )
      toFromBundleMsgBundle
  recvQueues <- reverse <$> readTVarIO recvQueuesAccum
  let recvQueues' = listArray (0, length recvQueues - 1) recvQueues
  _ <- forkIO $ demuxer @bundle bearer recvQueues'
  return chans

newMuxChanSingle ::
  forall bundle m a.
  (MonadMVar m, MonadSTM m) =>
  Chan m (BearerMsg (BundleMsg bundle)) ->
  MVar m () ->
  TVar m Int ->
  TVar m [RecvQueue m (BundleMsg bundle)] ->
  ToFromBundleMsg (BundleMsg bundle) a ->
  m (Chan m a)
newMuxChanSingle
  bearer
  sendLock
  recvQueuesIx
  recvQueuesAccum
  ToFromBundleMsg{..} = do
    queue <- newTQueueIO
    i <- atomically $ do
      modifyTVar recvQueuesAccum (RecvQueue fromBundleMsg queue :)
      i <- readTVar recvQueuesIx
      writeTVar recvQueuesIx $! (i + 1)
      return i
    return
      Chan
        { readChan = atomically (readTQueue queue)
        , writeChan = \msg ->
            let !muxmsg = BearerMsg i (toBundleMsg msg)
             in withMVar sendLock $ \_ -> writeChan bearer muxmsg
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
    BearerMsg i msg <- readChan bearer
    case queues ! i of
      RecvQueue convert queue ->
        atomically $ writeTQueue queue $! convert msg

data ExampleBundle f = ExampleBundle
  { exampleFoo :: f Int
  , exampleBar :: f Bool
  }

data ExampleMsg
  = MsgFoo {fromMsgFoo :: Int}
  | MsgBar {fromMsgBar :: Bool}

instance ConnectionBundle ExampleBundle where
  type BundleMsg ExampleBundle = ExampleMsg

  toFromBundleMsgBundle =
    ExampleBundle
      { exampleFoo = ToFromBundleMsg MsgFoo fromMsgFoo
      , exampleBar = ToFromBundleMsg MsgBar fromMsgBar
      }

  traverseConnectionBundle f ExampleBundle{..} =
    ExampleBundle
      <$> f exampleFoo
      <*> f exampleBar
