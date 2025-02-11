{-# LANGUAGE FlexibleInstances #-}

module PraosProtocol.SimChainSync where

import Chan.Driver (ProtocolMessage)
import Chan.TCP (
  LabelTcpDir,
  TcpConnProps,
  TcpEvent,
  newConnectionTCP,
 )
import Control.Monad.Class.MonadAsync (
  MonadAsync (concurrently_),
 )
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (..),
  Tracer (Tracer),
  traceWith,
 )
import qualified Data.ByteString as BS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import PraosProtocol.ChainSync (
  ChainConsumerState (..),
  ChainSyncState,
  runChainConsumer,
  runChainProducer,
 )
import PraosProtocol.Common hiding (Point)
import qualified PraosProtocol.Common.Chain as Chain
import STMCompat
import SimTCPLinks (
  labelDirToLabelLink,
  mkTcpConnProps,
  selectTimedEvents,
  simTracer,
 )
import SimTypes

type ChainSyncTrace = [(Time, ChainSyncEvent)]

data ChainSyncEvent
  = -- | Declare the nodes and links
    ChainSyncEventSetup
      !World
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    ChainSyncEventNode (LabelNode ChainSyncNodeEvent)
  | -- | An event on a tcp link between two nodes
    ChainSyncEventTcp (LabelLink (TcpEvent (ProtocolMessage ChainSyncState)))
  deriving (Show)

data ChainSyncNodeEvent = ChainSyncNodeEvent
  deriving (Show)

exampleTrace1 :: ChainSyncTrace
exampleTrace1 = traceRelayLink1 $ mkTcpConnProps 0.1 1000000

traceRelayLink1 ::
  TcpConnProps ->
  ChainSyncTrace
traceRelayLink1 tcpprops =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        ChainSyncEventSetup
          World
            { worldDimensions = (500, 500)
            , worldShape = Rectangle
            }
          ( Map.fromList
              [ (NodeId 0, Point 50 100)
              , (NodeId 1, Point 450 100)
              ]
          )
          ( Set.fromList
              [(NodeId 0, NodeId 1), (NodeId 1, NodeId 0)]
          )
      (inChan, outChan) <- newConnectionTCP (linkTracer na nb) tcpprops
      let praosConfig = defaultPraosConfig
      concurrently_
        (consumerNode praosConfig inChan)
        (producerNode outChan)
      return ()
 where
  consumerNode cfg chan = do
    let valHeader = threadDelay . cfg.headerValidationDelay
    st <- ChainConsumerState <$> newTVarIO Chain.Genesis <*> pure valHeader
    let nullTracer = Tracer $ const $ return ()
    runChainConsumer nullTracer cfg chan st
  producerNode chan = do
    let chain = mkChainSimple $ [BlockBody (BS.pack [i]) (kilobytes 95) | i <- [0 .. 10]]
    let (cps, fId) = initFollower GenesisPoint $ initChainProducerState chain
    st <- newTVarIO cps
    runChainProducer chan fId st

  (na, nb) = (NodeId 0, NodeId 1)

  tracer :: Tracer (IOSim s) ChainSyncEvent
  tracer = simTracer

  linkTracer ::
    NodeId ->
    NodeId ->
    Tracer
      (IOSim s)
      (LabelTcpDir (TcpEvent (ProtocolMessage ChainSyncState)))
  linkTracer nfrom nto =
    contramap (ChainSyncEventTcp . labelDirToLabelLink nfrom nto) tracer
