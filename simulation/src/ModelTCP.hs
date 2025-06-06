{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ModelTCP (
  Bytes (..),
  TcpConnProps (..),
  TcpState (..),
  initTcpState,
  saneTcpState,
  segmentSize,
  TcpMsgForecast (..),
  forecastTcpMsgSend,
  TcpEvent (..),
  traceTcpSend,
  mkTcpConnProps,
  kilobytes,
  segments,
  bytesToKb,
) where

import Control.Exception (assert)
import Data.Aeson
import Data.Foldable as Foldable (Foldable (sum, toList))
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.PQueue.Prio.Min (MinPQueue)
import qualified Data.PQueue.Prio.Min as PQ
import Data.Semigroup (Semigroup (sconcat))
import GHC.Generics
import SimTypes
import TimeCompat

-- | The fixed characteristics of this TCP link: the latency, bandwidth and
-- receiver window size. Each of these imposes a limit to effective
-- transmission speed.
data TcpConnProps = TcpConnProps
  { tcpLatency :: !DiffTime
  -- ^ The one-way transmission latency in seconds. Typical values
  -- would be 10s to 100s of milliseconds, e.g. 300ms for intercontinental
  -- links.
  , tcpBandwidth :: !Bytes
  -- ^ The sender serialisation bandwidth in bytes per sec. Typical values
  -- would be a few hundred kilobytes per second, e.g. 100 kb\/s is
  -- 0.8 MBit\/s, which is close to 1 MBit\/s once overheads are included.
  , tcpReceiverWindow :: !Bytes
  -- ^ The size of the receiver's window, which is an upper bound on the
  -- size of the congestion window.
  --
  -- This becomes a limit on the effective bandwidth if it is less than
  -- twice the bandwidth-latency product. That is, suppose the latency
  -- is 0.3s and the bandwidth is 100 kb\/s then the bandwidth-latency
  -- product is 30 kb, and so the receiver window must be at least 60 kb
  -- to avoid limiting the throughput.
  }
  deriving (Show)

mkTcpConnProps ::
  -- | latency in seconds
  DiffTime ->
  -- | sender serialisation bandwidth in bytes per sec, @Nothing@ for unlimited
  Bytes ->
  TcpConnProps
mkTcpConnProps latency bandwidth =
  TcpConnProps
    { tcpLatency = latency
    , tcpBandwidth = bandwidth
    , tcpReceiverWindow = max (segments 10) recvwnd
    }
 where
  -- set it big enough to not constrain the bandwidth
  recvwnd = Bytes (ceiling (fromIntegral (fromBytes bandwidth) * latency * 2))

kilobytes :: Int -> Bytes
kilobytes kb = Bytes kb * 1024

segments :: Int -> Bytes
segments s = Bytes s * segmentSize

-- | Rounds down.
bytesToKb :: Bytes -> Int
bytesToKb (Bytes b) = b `div` 1024

data TcpState = TcpState
  { tcpCongestionWindow :: !Bytes
  -- ^ The congestion window size.
  , tcpAvailableCongestionWindow :: !Bytes
  -- ^ The available portion of the congestion window that we can use to
  -- send more data. The remainder of the congestion window is tied up
  -- with in-flight data that is not yet acknowledged.
  , tcpAcknowledgements :: !(MinPQueue Time Bytes)
  -- ^ A collection of future TCP acknowledgements of data that we've sent.
  -- It is organised as a priority queue, ordered by the arrival time of
  -- each acknowledgement.
  }
  deriving (Show)

initTcpState :: TcpState
initTcpState =
  TcpState
    { tcpCongestionWindow = initialCongestionWindow
    , tcpAvailableCongestionWindow = initialCongestionWindow
    , tcpAcknowledgements = PQ.empty
    }

-- | The initial congestion window size is typically 10 segments
initialCongestionWindow :: Bytes
initialCongestionWindow = 10 * segmentSize

-- | A typical size for the TCP segment size.
segmentSize :: Bytes
segmentSize = 1460

saneTcpState :: TcpConnProps -> TcpState -> Bool
saneTcpState
  TcpConnProps{tcpReceiverWindow}
  TcpState
    { tcpCongestionWindow
    , tcpAvailableCongestionWindow
    , tcpAcknowledgements
    } =
    {-
        assert (tcpCongestionWindow <= tcpReceiverWindow) $
        assert (tcpCongestionWindow == tcpAvailableCongestionWindow
                                     + Foldable.sum tcpAcknowledgements) $
        True
    -}
    tcpCongestionWindow <= tcpReceiverWindow
      && tcpCongestionWindow
        == tcpAvailableCongestionWindow
          + Foldable.sum tcpAcknowledgements

data TcpMsgForecast = TcpMsgForecast
  { msgSendLeadingEdge :: !Time
  -- ^ The time the sender starts sending (leading edge);
  , msgSendTrailingEdge :: !Time
  -- ^ The time the sender finishes sending (trailing edge);
  , msgRecvLeadingEdge :: !Time
  -- ^ The time the message starts to arrive at the receiver (leading edge);
  , msgRecvTrailingEdge :: !Time
  -- ^ The time the message is fully received (trailing edge);
  , msgAcknowledgement :: !Time
  -- ^ The time the last acknowledgement returns to the sender;
  , msgSize :: !Bytes
  }
  deriving (Show, Generic, ToJSON, FromJSON)

-- | Merging forecasts takes the bounding intervals: earliest leading edge
-- and latest trailing edges.
instance Semigroup TcpMsgForecast where
  TcpMsgForecast{msgSendLeadingEdge, msgRecvLeadingEdge, msgSize = sz1}
    <> TcpMsgForecast
      { msgSendTrailingEdge
      , msgRecvTrailingEdge
      , msgSize = sz2
      , msgAcknowledgement
      } =
      TcpMsgForecast
        { msgSendLeadingEdge
        , msgSendTrailingEdge
        , msgRecvLeadingEdge
        , msgRecvTrailingEdge
        , msgAcknowledgement
        , msgSize = sz1 + sz2
        }

forecastTcpMsgSend ::
  TcpConnProps ->
  TcpState ->
  -- | initial time of msg send
  Time ->
  -- | message size
  Bytes ->
  (TcpMsgForecast, [TcpMsgForecast], TcpState)
forecastTcpMsgSend
  TcpConnProps{tcpLatency, tcpBandwidth, tcpReceiverWindow}
  tcpstate0
  now0
  msgsize0 =
    let (forecasts, !tcpstate) = trySend [] tcpstate0 now0 msgsize0
        !mergedForecasts = mergeAdjacentForecasts forecasts
        !overallforecast = sconcat mergedForecasts
     in (overallforecast, toList mergedForecasts, tcpstate)
   where
    trySend ::
      [TcpMsgForecast] ->
      TcpState ->
      Time ->
      Bytes ->
      (NonEmpty TcpMsgForecast, TcpState)

    trySend forecasts !tcpstate !now !msgsize
      -- If the available congestion window is empty, we have to wait for an
      -- acknowledgement to arrive, to increase the available congestion window
      -- This may also increase the congestion window too, if it's not yet hit
      -- the upper limit of the receiver window size.
      | tcpAvailableCongestionWindow tcpstate == 0 =
          let (now', tcpstate') = waitForAck now tcpstate
           in trySend forecasts tcpstate' now' msgsize
      -- If the entire message fits into the available congestion window, we
      -- can send it all now without waiting.
      | msgsize <= tcpAvailableCongestionWindow tcpstate =
          let (forecast, tcpstate') = send tcpstate now msgsize
           in (NE.reverse (forecast :| forecasts), tcpstate')
      -- The message does not fit into the available congestion window, but the
      -- available congestion  window is not empty, so we send a prefix of the
      -- message, leaving the available congestion  window empty.
      | otherwise =
          let sendsize = tcpAvailableCongestionWindow tcpstate
              msgsize' = msgsize - sendsize
              (forecast, tcpstate') = send tcpstate now sendsize
              now' = msgSendTrailingEdge forecast
           in trySend (forecast : forecasts) tcpstate' now' msgsize'

    send :: TcpState -> Time -> Bytes -> (TcpMsgForecast, TcpState)
    send tcpstate now sendsize =
      ( TcpMsgForecast
          { msgSendLeadingEdge
          , msgSendTrailingEdge
          , msgRecvLeadingEdge
          , msgRecvTrailingEdge
          , msgAcknowledgement
          , msgSize = sendsize
          }
      , tcpstate'
      )
     where
      !tcpstate' =
        tcpstate
          { tcpAvailableCongestionWindow =
              tcpAvailableCongestionWindow tcpstate - sendsize
          , tcpAcknowledgements =
              PQ.insert
                msgAcknowledgement
                sendsize
                (tcpAcknowledgements tcpstate)
          }
      msgSendLeadingEdge = now
      msgSendTrailingEdge =
        serialisationTime sendsize
          `addTime` msgSendLeadingEdge
      msgRecvLeadingEdge = tcpLatency `addTime` msgSendLeadingEdge
      msgRecvTrailingEdge = tcpLatency `addTime` msgSendTrailingEdge
      msgAcknowledgement = tcpLatency `addTime` msgRecvLeadingEdge
    -- \^^ this is strategic cheating, using the recv
    -- leading rather than trailing edge

    -- The model would work correctly if we just grabbed the next ack, and thus
    -- sent just enough message data allowed by that ack, however over time that
    -- leads to an ever increasing number of acks and message fragments. To see
    -- this note that sending a message can lead to multiple acks but there is
    -- otherwise no mechanism to "merge" acks, hence ever increasing
    -- fragmentation.
    --
    -- So instead what we do here is to grab /all/ acks that have already
    -- arrived, or if none have arrived, wait for the next one. It is the
    -- grabbing and merging of multiple acks that should keep fragmentation
    -- under control.
    --
    waitForAck :: Time -> TcpState -> (Time, TcpState)
    waitForAck now tcpstate@TcpState{tcpAcknowledgements} =
      case PQ.minViewWithKey tcpAcknowledgements of
        Nothing -> error "forecastTcpMsgSend: empty window with no acks"
        Just ((ackts, ackbytes), tcpAcknowledgements')
          | ackts <= now ->
              (now, tcpstate')
         where
          tcpstate' =
            arrivedAcks now $
              accumAck tcpstate ackbytes tcpAcknowledgements'
        Just ((ackts, ackbytes), tcpAcknowledgements') ->
          (now', tcpstate')
         where
          now' = ackts
          tcpstate' = accumAck tcpstate ackbytes tcpAcknowledgements'

    arrivedAcks :: Time -> TcpState -> TcpState
    arrivedAcks !now tcpstate@TcpState{tcpAcknowledgements} =
      case PQ.minViewWithKey tcpAcknowledgements of
        Just ((ackts, ackbytes), tcpAcknowledgements')
          | ackts <= now ->
              arrivedAcks now tcpstate'
         where
          tcpstate' = accumAck tcpstate ackbytes tcpAcknowledgements'
        Just _ -> tcpstate
        Nothing -> tcpstate

    -- How we update is different if we're still expanding our congestion
    -- window, vs when we hit a steady state of the congestion window
    -- maxing out at the receiver window size. If we're still expanding
    -- then we expand our congestion window by the acknowledged bytes too,
    -- with the receiver window as an upper limit. That means the available
    -- part of the window increases by the acknowledged bytes plus the
    -- expansion of the congestion window.
    accumAck :: TcpState -> Bytes -> MinPQueue Time Bytes -> TcpState
    accumAck
      tcpstate@TcpState
        { tcpCongestionWindow
        , tcpAvailableCongestionWindow
        }
      ackbytes
      tcpAcknowledgements'
        | tcpCongestionWindow < tcpReceiverWindow =
            tcpstate
              { tcpCongestionWindow = tcpCongestionWindow'
              , tcpAvailableCongestionWindow = tcpAvailableCongestionWindow'
              , tcpAcknowledgements = tcpAcknowledgements'
              }
       where
        tcpCongestionWindow' =
          min tcpReceiverWindow (tcpCongestionWindow + ackbytes)
        tcpAvailableCongestionWindow' =
          tcpAvailableCongestionWindow
            + ackbytes
            + (tcpCongestionWindow' - tcpCongestionWindow)

    -- Otherwise the congestion window is the size of the receiver window
    -- and we just increase the available part by the acknowledged bytes.
    accumAck
      tcpstate@TcpState
        { tcpCongestionWindow
        , tcpAvailableCongestionWindow
        }
      ackbytes
      tcpAcknowledgements' =
        assert (tcpCongestionWindow == tcpReceiverWindow) $
          tcpstate
            { tcpAvailableCongestionWindow =
                tcpAvailableCongestionWindow
                  + ackbytes
            , tcpAcknowledgements = tcpAcknowledgements'
            }

    serialisationTime :: Bytes -> DiffTime
    serialisationTime msg =
      secondsToDiffTime (fromIntegral (fromBytes msg) / fromIntegral (fromBytes tcpBandwidth))

-- | To make the result easier to interpret, merge together any fragments
-- that are in fact contiguous.
mergeAdjacentForecasts :: NonEmpty TcpMsgForecast -> NonEmpty TcpMsgForecast
mergeAdjacentForecasts (forecast0 :| forecasts0) =
  case go forecast0 forecasts0 of
    [] -> error "internal: merged into empty"
    (x : xs) -> x :| xs
 where
  go forecast (forecast' : forecasts)
    | msgSendTrailingEdge forecast == msgSendLeadingEdge forecast' =
        go (forecast <> forecast') forecasts
    | otherwise =
        forecast : go forecast' forecasts
  go forecast [] =
    [forecast]

data TcpEvent msg
  = TcpSendMsg
      msg
      TcpMsgForecast -- overall
      [TcpMsgForecast] -- tcp internal activity
  deriving (Show, Functor)

traceTcpSend ::
  TcpConnProps ->
  -- | message sizes to send eagerly, back-to-back
  [Bytes] ->
  [TcpEvent ()] -- trace of TCP behaviour
traceTcpSend tcpprops =
  -- assert (recvwnd >= initcwnd) $ --TODO saneTcpConnProps
  go (Time 0) initTcpState
 where
  go ::
    Time ->
    TcpState ->
    [Bytes] -> -- messages to send
    [TcpEvent ()]
  go _ _ [] = []
  go now tcpstate (msg : msgs) =
    let (msgforecast, msgfragforecasts, tcpstate') =
          forecastTcpMsgSend tcpprops tcpstate now msg
        now' = msgSendTrailingEdge msgforecast
     in TcpSendMsg () msgforecast msgfragforecasts
          : go now' tcpstate' msgs
