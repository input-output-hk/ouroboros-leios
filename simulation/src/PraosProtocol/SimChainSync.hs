{-# LANGUAGE FlexibleInstances #-}

module PraosProtocol.SimChainSync where

import ChanDriver (ProtocolMessage, chanDriver)
import ChanTCP (
  LabelTcpDir,
  TcpConnProps,
  TcpEvent,
  newConnectionTCP,
 )
import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.Monad.Class.MonadAsync (
  MonadAsync (concurrently_),
 )
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import qualified Data.ByteString as BS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Network.TypedProtocol (runPeerWithDriver)
import PraosProtocol.ChainSync (
  ChainSyncState,
  chainConsumer,
  chainProducer,
  decideChainSyncState,
 )
import PraosProtocol.Common hiding (Point)
import qualified PraosProtocol.Common.Chain as Chain
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
      !WorldShape
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    ChainSyncEventNode (LabelNode ChainSyncNodeEvent)
  | -- | An event on a tcp link between two nodes
    ChainSyncEventTcp (LabelLink (TcpEvent (ProtocolMessage ChainSyncState)))
  deriving (Show)

type ChainSyncMessage = ProtocolMessage ChainSyncState

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
          WorldShape
            { worldDimensions = (500, 500)
            , worldIsCylinder = False
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
      concurrently_
        (consumerNode inChan)
        (producerNode outChan)
      return ()
 where
  consumerNode chan = do
    hchainVar <- newTVarIO Chain.Genesis
    runPeerWithDriver (chanDriver decideChainSyncState chan) (chainConsumer hchainVar)
  producerNode chan = do
    let chain = mkChainSimple $ replicate 10 (BlockBody $ BS.replicate 100 0)
    let (cps, fId) = initFollower GenesisPoint $ initChainProducerState chain
    cpsVar <- newTVarIO cps
    runPeerWithDriver (chanDriver decideChainSyncState chan) (chainProducer fId cpsVar)

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