{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SimTCPLinks where

import Data.Bifoldable
import Data.Dynamic

import Control.Monad
import Control.Monad.Class.MonadTime.SI
import Control.Monad.Class.MonadTimer
import Control.Monad.Class.MonadAsync
import Control.Concurrent.Class.MonadSTM
import Control.Tracer as Tracer

import TimeCompat (threadDelaySI)

import Control.Monad.IOSim as IOSim

import Chan
import ModelTCP
import ChanTCP
import SimTypes

------------------------------------------------------------------------------
-- Simulations
--

type TcpSimTrace = [(Time, TcpSimEvent)]

data TcpSimEvent =
       -- | Declare the nodes and links
       TcpSimEventSetup [(NodeId, (Int, Int))] [(NodeId, NodeId)]

       -- | An event at a node
     | TcpSimEventNode (LabelNode (NodeEvent TestMessage))

       -- | An event on a tcp link between two nodes
     | TcpSimEventTcp (LabelLink (TcpEvent TestMessage))
  deriving Show

data NodeEvent msg =
       MsgArrive msg
     | MsgDepart msg
  deriving Show

data TestMessage = TestMessage MsgId Bytes 
  deriving (Eq, Show)

type MsgId = Int

instance MessageSize TestMessage where
  messageSizeBytes (TestMessage _ bytes) = bytes

mkTcpConnProps :: DiffTime     -- ^ latency in seconds
               -> Bytes        -- ^ sender serialisation bandwidth in bytes per sec
               -> TcpConnProps
mkTcpConnProps latency bandwidth =
    TcpConnProps {
      tcpLatency        = latency,
      tcpBandwidth      = bandwidth,
      tcpReceiverWindow = max (segments 10) recvwnd
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


-- | A discription of a flow of test messages over a single TCP link.
-- Used in test setups.
-- 
data TrafficPattern =
       UniformTrafficPattern
         Int              -- number of messages
         Bytes            -- size of each message
         (Maybe DiffTime) -- delay between each message

mkEagerUniformTrafficPattern :: Int   -- ^ number of messages to send eagerly, back-to-back
                             -> Bytes -- ^ message size
                             -> TrafficPattern
mkEagerUniformTrafficPattern nmsgs msgsz =
    UniformTrafficPattern nmsgs msgsz Nothing

mkUniformTrafficPattern :: Int   -- ^ number of messages to send eagerly, back-to-back
                             -> Bytes -- ^ message size
                             -> DiffTime
                             -> TrafficPattern
mkUniformTrafficPattern nmsgs msgsz senddelay =
    UniformTrafficPattern nmsgs msgsz (Just senddelay)

--
-- Individual nodes
--

generatorNode :: MonadDelay m
              => Tracer m (NodeEvent TestMessage)
              -> TrafficPattern
              -> Chan m TestMessage
              -> m ()
generatorNode tracer (UniformTrafficPattern nmsgs msgsz mdelay) chan = do
    sequence_
      [ traceWith tracer (MsgArrive msg)
      | msg <- map (flip TestMessage msgsz) [0..nmsgs-1] ]
    sequence_
      [ do writeChan chan msg
           traceWith tracer (MsgDepart msg)
           maybe (return ()) threadDelaySI mdelay
      | msg <- map (flip TestMessage msgsz) [0..nmsgs-1] ]

sinkNode :: Monad m
         => Tracer m (NodeEvent TestMessage)
         -> TrafficPattern
         -> Chan m TestMessage
         -> m ()
sinkNode tracer (UniformTrafficPattern nmsgs _ _) chan =
    replicateM_ nmsgs $ do
      msg <- readChan chan
      traceWith tracer (MsgArrive msg)

relayNode :: MonadAsync m
          => Tracer m (NodeEvent TestMessage)
          -> TrafficPattern
          -> Chan m TestMessage
          -> Chan m TestMessage
          -> m ()
relayNode tracer (UniformTrafficPattern nmsgs _ _) outchan inchan = do
    -- "out" and "in" chan names are from the perspective of the channel,
    -- not the relayNode. So we read from the out chan and write to the in chan.

    -- Rather than read one; write one, we eagerly pull messages from one
    -- channel, and buffer them at the "app" level. This makes the message
    -- arrival times visible in the trace.
    q <- newTQueueIO
    concurrently_
      (replicateM_ nmsgs $ do
         msg <- readChan outchan
         traceWith tracer (MsgArrive msg)
         atomically $ writeTQueue q msg)
      (replicateM_ nmsgs $ do
         msg <- atomically $ readTQueue q
         writeChan inchan msg
         traceWith tracer (MsgDepart msg))


--
-- Overall simulations
--

labelDirToLabelLink :: NodeId -> NodeId -> LabelTcpDir e -> LabelLink e
labelDirToLabelLink nfrom nto (DirClientToServer e) = LabelLink nfrom nto e
labelDirToLabelLink nfrom nto (DirServerToClient e) = LabelLink nto nfrom e

simTracer :: Typeable e => Tracer (IOSim s) e
simTracer = Tracer.Tracer $ Tracer.emit $ IOSim.traceM


selectTimedEvents :: forall a b. Typeable b => SimTrace a -> [(Time, b)]
selectTimedEvents =
    bifoldr ( \ _ _   -> []  )
            ( \ b acc -> case b of
                           SimEvent { seTime, seType }
                             | Just b' <- selectDynamic seType
                             -> (seTime, b') : acc
                           _ -> acc
            )
            []
  where
    selectDynamic :: SimEventType -> Maybe b
    selectDynamic (EventLog dyn) = fromDynamic dyn
    selectDynamic _              = Nothing


traceTcpLinks1 :: TcpConnProps
               -> TrafficPattern
               -> TcpSimTrace
traceTcpLinks1 tcpprops trafficPattern =
    selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        TcpSimEventSetup
          [(NodeId 0, (50,  50)),
           (NodeId 1, (450, 50))]
          [(NodeId 0, NodeId 1)]
      (inChan, outChan) <- newConnectionTCP (linkTracer na nb) tcpprops
      concurrently_
        (generatorNode (nodeTracer na) trafficPattern inChan)
        (sinkNode      (nodeTracer nb) trafficPattern outChan)
  where
    [na, nb] = map NodeId [0, 1]

    tracer :: Tracer (IOSim s) TcpSimEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) (NodeEvent TestMessage)
    nodeTracer n =
      contramap (TcpSimEventNode . LabelNode n) tracer

    linkTracer :: NodeId -> NodeId
               -> Tracer (IOSim s) (LabelTcpDir (TcpEvent TestMessage))
    linkTracer nfrom nto =
      contramap (TcpSimEventTcp . labelDirToLabelLink nfrom nto) tracer

traceTcpLinks4 :: TcpConnProps
               -> TcpConnProps
               -> TcpConnProps
               -> TrafficPattern
               -> TcpSimTrace
traceTcpLinks4 a2bTcpProps b2cTcpProps c2dTcpProps trafficPattern =
    selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        TcpSimEventSetup
          [(NodeId 0, ( 50, 70)),
           (NodeId 1, (350, 70)),
           (NodeId 2, (650, 70)),
           (NodeId 3, (950, 70))]
          [(NodeId 0, NodeId 1),
           (NodeId 1, NodeId 2),
           (NodeId 2, NodeId 3)]
      (a2bInChan, a2bOutChan) <- newConnectionTCP (linkTracer na nb) a2bTcpProps
      (b2cInChan, b2cOutChan) <- newConnectionTCP (linkTracer nb nc) b2cTcpProps
      (c2dInChan, c2dOutChan) <- newConnectionTCP (linkTracer nc nd) c2dTcpProps
      runConcurrently $
        () <$ Concurrently (generatorNode (nodeTracer na)
                                          trafficPattern a2bInChan)
           <* Concurrently (relayNode     (nodeTracer nb)
                                          trafficPattern a2bOutChan b2cInChan)
           <* Concurrently (relayNode     (nodeTracer nc)
                                          trafficPattern b2cOutChan c2dInChan)
           <* Concurrently (sinkNode      (nodeTracer nd)
                                          trafficPattern c2dOutChan)
  where
    [na, nb, nc, nd] = map NodeId [0..3]

    tracer :: Tracer (IOSim s) TcpSimEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) (NodeEvent TestMessage)
    nodeTracer n =
      contramap (TcpSimEventNode . LabelNode n) tracer

    linkTracer :: NodeId -> NodeId
               -> Tracer (IOSim s) (LabelTcpDir (TcpEvent TestMessage))
    linkTracer nfrom nto =
      contramap (TcpSimEventTcp . labelDirToLabelLink nfrom nto) tracer

