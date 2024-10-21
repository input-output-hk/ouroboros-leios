{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module PraosProtocol.SimBlockFetch where

import ChanDriver
import ChanTCP
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
import Network.TypedProtocol
import PraosProtocol.BlockFetch
import PraosProtocol.Common hiding (Point)
import qualified PraosProtocol.Common.Chain as Chain
import SimTCPLinks
import SimTypes

type BlockFetchTrace = [(Time, BlockFetchEvent)]

data BlockFetchEvent
  = -- | Declare the nodes and links
    BlockFetchEventSetup
      !WorldShape
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    BlockFetchEventNode (LabelNode BlockFetchNodeEvent)
  | -- | An event on a tcp link between two nodes
    BlockFetchEventTcp (LabelLink (TcpEvent (ProtocolMessage BlockFetchState)))
  deriving (Show)
type BlockFetchMessage = ProtocolMessage BlockFetchState
data BlockFetchNodeEvent = BlockFetchNodeEvent
  -- = RelayNodeEventGenerate blk

  deriving
    ( -- | RelayNodeEventEnterQueue blk
      -- | RelayNodeEventEnterBuffer blk
      -- | RelayNodeEventRemove blk
      Show
    )

exampleTrace1 :: BlockFetchTrace
exampleTrace1 = traceRelayLink1 $ mkTcpConnProps 0.1 1000000

traceRelayLink1 ::
  TcpConnProps ->
  --- PacketGenerationPattern ->
  BlockFetchTrace
traceRelayLink1 tcpprops =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        BlockFetchEventSetup
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
    runPeerWithDriver (chanDriver decideBlockFetchState chan) (chainConsumer hchainVar)
  producerNode chan = do
    let chain = mkChainSimple $ replicate 10 (BlockBody $ BS.replicate 100 0)
    let (cps, fId) = initFollower GenesisPoint $ initChainProducerState chain
    cpsVar <- newTVarIO cps
    runPeerWithDriver (chanDriver decideBlockFetchState chan) (chainProducer fId cpsVar)

  [na, nb] = map NodeId [0, 1]

  tracer :: Tracer (IOSim s) BlockFetchEvent
  tracer = simTracer

  linkTracer ::
    NodeId ->
    NodeId ->
    Tracer
      (IOSim s)
      (LabelTcpDir (TcpEvent (ProtocolMessage BlockFetchState)))
  linkTracer nfrom nto =
    contramap (BlockFetchEventTcp . labelDirToLabelLink nfrom nto) tracer
