{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module ChanMux (
  newMuxChan,
  Chan (..),
) where

import Data.Array

import Control.Concurrent.Class.MonadMVar
import Control.Concurrent.Class.MonadSTM
import Control.Monad
import Control.Monad.Class.MonadFork

import Chan

class MuxBundle bundle where
  type MuxMsg bundle
  toFromMuxMsgBundle :: bundle (ToFromMuxMsg (MuxMsg bundle))

  traverseMuxBundle ::
    Monad m =>
    (forall a. f a -> m (g a)) ->
    bundle f ->
    m (bundle g)

-- | Injection, projection, between a common mux message type, and an
-- individual message type. The following must hold:
--
-- > fromMuxMsg (toMuxMsg x) = x
--
-- But 'fromMuxMsg' is not required to be defined outside of the image of
-- 'toMuxMsg'. For example, a valid implementation would be:
--
-- > ToFromMuxMsg toDynamic (fromJust . fromDynamic)
data ToFromMuxMsg mm a
  = ToFromMuxMsg
  { toMuxMsg :: a -> mm
  , fromMuxMsg :: mm -> a
  }

data BearerMsg a = BearerMsg !Int a

newMuxChan ::
  forall bundle m.
  (MuxBundle bundle, MonadMVar m, MonadSTM m, MonadFork m) =>
  Chan m (BearerMsg (MuxMsg bundle)) ->
  m (bundle (Chan m))
newMuxChan bearer = do
  sendLock <- newMVar ()
  -- Bit of a hack to use these TVars, could run the traverseMuxBundle
  -- in a reader+state monad instead. That'd be cleaner.
  recvQueuesAccum <- newTVarIO []
  recvQueuesIx <- newTVarIO 0
  chans <-
    traverseMuxBundle
      ( newMuxChanSingle @bundle
          bearer
          sendLock
          recvQueuesIx
          recvQueuesAccum
      )
      toFromMuxMsgBundle
  recvQueues <- reverse <$> readTVarIO recvQueuesAccum
  let recvQueues' = listArray (0, length recvQueues - 1) recvQueues
  _ <- forkIO $ demuxer @bundle bearer recvQueues'
  return chans

newMuxChanSingle ::
  forall bundle m a.
  (MonadMVar m, MonadSTM m) =>
  Chan m (BearerMsg (MuxMsg bundle)) ->
  MVar m () ->
  TVar m Int ->
  TVar m [RecvQueue m (MuxMsg bundle)] ->
  ToFromMuxMsg (MuxMsg bundle) a ->
  m (Chan m a)
newMuxChanSingle
  bearer
  sendLock
  recvQueuesIx
  recvQueuesAccum
  ToFromMuxMsg{..} = do
    queue <- newTQueueIO
    i <- atomically $ do
      modifyTVar recvQueuesAccum (RecvQueue fromMuxMsg queue :)
      i <- readTVar recvQueuesIx
      writeTVar recvQueuesIx $! (i + 1)
      return i
    return
      Chan
        { readChan = atomically (readTQueue queue)
        , writeChan = \msg ->
            let !muxmsg = BearerMsg i (toMuxMsg msg)
             in withMVar sendLock $ \_ -> writeChan bearer muxmsg
        }

data RecvQueue m mm where
  RecvQueue :: (mm -> a) -> TQueue m a -> RecvQueue m mm

demuxer ::
  forall bundle m.
  MonadSTM m =>
  Chan m (BearerMsg (MuxMsg bundle)) ->
  Array Int (RecvQueue m (MuxMsg bundle)) ->
  m ()
demuxer bearer queues =
  forever $ do
    BearerMsg i msg <- readChan bearer
    case queues ! i of
      RecvQueue convert queue ->
        atomically $ writeTQueue queue $! (convert msg)

data ExampleBundle f = ExampleBundle
  { exampleFoo :: f Int
  , exampleBar :: f Bool
  }

data ExampleMsg
  = MsgFoo {fromMsgFoo :: Int}
  | MsgBar {fromMsgBar :: Bool}

instance MuxBundle ExampleBundle where
  type MuxMsg ExampleBundle = ExampleMsg

  toFromMuxMsgBundle =
    ExampleBundle
      { exampleFoo = ToFromMuxMsg MsgFoo fromMsgFoo
      , exampleBar = ToFromMuxMsg MsgBar fromMsgBar
      }

  traverseMuxBundle f ExampleBundle{..} =
    ExampleBundle
      <$> f exampleFoo
      <*> f exampleBar
