{-# LANGUAGE RecordWildCards #-}

module Chan.Simple (
  SimpleConnProps (..),
  newConnectionSimple,
) where

import Chan.Core (Chan (..))
import Chan.TCP (LabelTcpDir (..), MessageSize (..), RecvBuf, SendBuf, TcpEvent (..), TcpMsgForecast (..), mkChan, newRecvBuf, newSendBuf)
import Control.Monad.Class.MonadAsync (MonadAsync (..))
import Control.Tracer as Tracer (Contravariant (..), Tracer, traceWith)
import ModelTCP (Bytes)
import STMCompat
import TimeCompat

data SimpleConnProps = SimpleConnProps
  { latency :: DiffTime
  , bandwidthBytesPerSecond :: Maybe Bytes
  }

newConnectionSimple ::
  forall m a.
  (MonadTime m, MonadMonotonicTimeNSec m, MonadDelay m, MonadAsync m, MessageSize a) =>
  Tracer m (LabelTcpDir (TcpEvent a)) ->
  SimpleConnProps ->
  m (Chan m a, Chan m a)
newConnectionSimple tracer simpleConnProps = do
  clientSendBuf <- newSendBuf
  serverSendBuf <- newSendBuf
  clientRecvBuf <- newRecvBuf
  serverRecvBuf <- newRecvBuf

  _ <-
    async
      ( transport
          (contramap DirClientToServer tracer)
          simpleConnProps
          clientSendBuf
          serverRecvBuf
      )
  _ <-
    async
      ( transport
          (contramap DirServerToClient tracer)
          simpleConnProps
          serverSendBuf
          clientRecvBuf
      )

  let clientChan, serverChan :: Chan m a
      clientChan = mkChan clientSendBuf clientRecvBuf
      serverChan = mkChan serverSendBuf serverRecvBuf

  return (clientChan, serverChan)

transport ::
  (MonadSTM m, MonadMonotonicTimeNSec m, MonadDelay m, MessageSize a) =>
  Tracer m (TcpEvent a) ->
  SimpleConnProps ->
  SendBuf m a ->
  RecvBuf m a ->
  m ()
transport tracer SimpleConnProps{..} sendbuf recvbuf = go
 where
  go = do
    msg <- atomically $ readTMVar sendbuf -- read now but keep buffer full
    now <- getMonotonicTime

    let msgSize = messageSizeBytes msg
        msgSerialisationTime = case bandwidthBytesPerSecond of
          Nothing -> 0
          Just bps -> fromIntegral msgSize / fromIntegral bps
        msgSendLeadingEdge = now
        msgSendTrailingEdge = msgSerialisationTime `addTime` now
        msgRecvLeadingEdge = latency `addTime` now
        msgRecvTrailingEdge = latency `addTime` msgSendTrailingEdge
        msgAcknowledgement = latency `addTime` msgRecvTrailingEdge
    let msgForecast = TcpMsgForecast{..}

    -- schedule the arrival, and wait until it has finished sending
    atomically $ writeTQueue recvbuf (msgRecvTrailingEdge, msg)
    traceWith tracer (TcpSendMsg msg msgForecast [])
    threadDelay (msgSendTrailingEdge `diffTime` now)
    -- We keep the sendbuf full until the message has finished sending
    -- so that there's less buffering, and better simulates the TCP buffer
    -- rather than an extra app-level buffer.
    _ <- atomically $ takeTMVar sendbuf
    go
