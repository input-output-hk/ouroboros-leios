{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Chan.TCP (
  module Chan.TCP,
  module ModelTCP,
) where

import Chan.Core (Chan (..))
import Control.Exception (assert)
import Control.Monad (when)
import Control.Monad.Class.MonadAsync (MonadAsync (async))
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import qualified Data.PQueue.Prio.Min as PQ
import ModelTCP (
  Bytes,
  TcpConnProps (..),
  TcpEvent (..),
  TcpMsgForecast (..),
  TcpState (..),
  forecastTcpMsgSend,
  initTcpState,
  saneTcpState,
 )
import STMCompat
import TimeCompat

-- | In the scope of a two party connection, there are just two peers. These
-- can be maped to a wider scope peer identity via contra-trace.
data LabelTcpDir e = DirClientToServer e | DirServerToClient e
  deriving (Eq, Ord, Show, Functor)

lensLabelTcpDir :: Functor f => (a -> f b) -> LabelTcpDir a -> f (LabelTcpDir b)
lensLabelTcpDir f = \case
    DirClientToServer x -> DirClientToServer <$> f x
    DirServerToClient x -> DirServerToClient <$> f x

-- | Class for messages to be sent over a simulated TCP connection.
-- To correctly model the timing of the messages sent over the connection we
-- need to know a reasonable approximation of the message size. This does not
-- need to be totally accurate. Accuracy to the nearest TCP segment (~1400b)
-- is plenty.
class MessageSize msg where
  messageSizeBytes :: msg -> Bytes

instance (MessageSize a, MessageSize b) => MessageSize (a, b) where
  messageSizeBytes (a, b) = messageSizeBytes a + messageSizeBytes b

-- | Make a pair of 'Chan's, connected with a simulated bi-directional bearer
-- that emulates simple TCP performance behaviour.
--
-- It is given a one-way latency in seconds (with high precision).
--
-- Message order is preserved.
-- Otherwise buffers are assumed unbounded, and the latency is assumed to be
-- symmetric and without jitter.
newConnectionTCP ::
  forall m a.
  (MonadTime m, MonadMonotonicTimeNSec m, MonadDelay m, MonadAsync m, MessageSize a) =>
  Tracer m (LabelTcpDir (TcpEvent a)) ->
  TcpConnProps ->
  m (Chan m a, Chan m a)
newConnectionTCP tracer tcpprops = do
  clientSendBuf <- newSendBuf
  serverSendBuf <- newSendBuf
  clientRecvBuf <- newRecvBuf
  serverRecvBuf <- newRecvBuf

  _ <-
    async
      ( transport
          (contramap DirClientToServer tracer)
          tcpprops
          clientSendBuf
          serverRecvBuf
      )
  _ <-
    async
      ( transport
          (contramap DirServerToClient tracer)
          tcpprops
          serverSendBuf
          clientRecvBuf
      )

  let clientChan, serverChan :: Chan m a
      clientChan = mkChan clientSendBuf clientRecvBuf
      serverChan = mkChan serverSendBuf serverRecvBuf

  return (clientChan, serverChan)

type SendBuf m a = TMVar m a
type RecvBuf m a = TQueue m (Time, a)

newSendBuf :: MonadSTM m => m (SendBuf m a)
newSendBuf = newEmptyTMVarIO

newRecvBuf :: MonadSTM m => m (RecvBuf m a)
newRecvBuf = newTQueueIO

writeSendBuf :: MonadSTM m => SendBuf m a -> a -> m ()
writeSendBuf sendbuf msg = atomically (putTMVar sendbuf msg)

readRecvBuf ::
  (MonadSTM m, MonadMonotonicTimeNSec m, MonadDelay m) =>
  RecvBuf m a ->
  m a
readRecvBuf recvbuf = do
  (arrivaltime, msg) <- atomically $ readTQueue recvbuf

  now <- getMonotonicTime
  let delay = arrivaltime `diffTime` now
  when (delay > 0) (threadDelay delay)
  return msg

mkChan ::
  (MonadSTM m, MonadMonotonicTimeNSec m, MonadDelay m) =>
  SendBuf m a ->
  RecvBuf m a ->
  Chan m a
mkChan sendbuf recvbuf =
  Chan
    { readChan = readRecvBuf recvbuf
    , writeChan = writeSendBuf sendbuf
    }

transport ::
  (MonadSTM m, MonadMonotonicTimeNSec m, MonadDelay m, MessageSize a) =>
  Tracer m (TcpEvent a) ->
  TcpConnProps ->
  SendBuf m a ->
  RecvBuf m a ->
  m ()
transport tracer tcpprops sendbuf recvbuf = do
  go initTcpState
 where
  go tcpstate = assert (saneTcpState tcpprops tcpstate) $ do
    -- wait for the next message to send
    now <- getMonotonicTime
    msg <- atomically $ readTMVar sendbuf -- read now but keep buffer full
    now' <- getMonotonicTime

    -- if the connection was idle too long, reset the window size
    let tcpstate' :: TcpState
        tcpstate'
          | tcpIdleResetTime tcpprops now <= now' =
              let allAcksArrived =
                    PQ.foldrWithKeyU
                      (\t _ ok -> t <= now' && ok)
                      True
                      (tcpAcknowledgements tcpstate)
               in assert allAcksArrived initTcpState
          | otherwise =
              tcpstate

    -- send it
    let msgsize = messageSizeBytes msg
        ( forecast@TcpMsgForecast
            { msgSendTrailingEdge
            , msgRecvTrailingEdge
            }
          , tcpforecasts
          , tcpstate''
          ) = assert (msgsize > 0) $ forecastTcpMsgSend tcpprops tcpstate' now' msgsize

    -- schedule the arrival, and wait until it has finished sending
    atomically $ writeTQueue recvbuf (msgRecvTrailingEdge, msg)
    traceWith tracer (TcpSendMsg msg forecast tcpforecasts)
    threadDelay (msgSendTrailingEdge `diffTime` now')
    -- We keep the sendbuf full until the message has finished sending
    -- so that there's less buffering, and better simulates the TCP buffer
    -- rather than an extra app-level buffer.
    _ <- atomically $ takeTMVar sendbuf
    go tcpstate''

-- | RFC 6298 provides an algorithm for computing the RTO, which is also used
-- for the timeout for resetting to the initial congestion window size.
-- We could do that, but the algorithm also uses a minimum of 1s, which appears
-- to be the limit in practice. It converges to 1 RTT if there's not much
-- jitter. So we just use the max of the RTT and 1s.
--
-- The signature and order of operations is awkward here because it needs to
-- exactly match an assertion near the use case, since these types are
-- represented as 'Double's.
tcpIdleResetTime :: TcpConnProps -> Time -> Time
tcpIdleResetTime TcpConnProps{tcpLatency} t =
  max (1 `addTime` t) (tcpLatency `addTime` (tcpLatency `addTime` t))
