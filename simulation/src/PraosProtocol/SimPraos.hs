{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PraosProtocol.SimPraos where

import ChanTCP
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
import PraosProtocol.BlockFetch
import PraosProtocol.ChainSync (ChainSyncMessage)
import PraosProtocol.Common hiding (Point)
import PraosProtocol.Common.Chain (Chain (..))
import PraosProtocol.PraosNode (Praos (..), runPraosNode)
import SimTCPLinks
import SimTypes

-- newConnectionTCP ::
--   forall (m :: Type -> Type).
--   (MonadTime m, MonadMonotonicTime m, MonadDelay m, MonadAsync m) =>
--   Tracer m (LabelTcpDir (TcpEvent ChainSyncMessage)) ->
--   Tracer m (LabelTcpDir (TcpEvent BlockFetchMessage)) ->
--   TcpConnProps ->
--   m (Praos (Chan m), Praos (Chan m))
-- newConnectionTCP chainSyncTracer blockFetchTracer tcpConnProps = do
--   (chainSyncProducerChan, chainSyncConsumerChan) <-
--     newConnectionTCP chainSyncTracer tcpConnProps
--   (blockFetchProducerChan, blockFetchOConsumerChan) <-
--     newConnectionTCP blockFetchTracer tcpConnProps
--   return (Praos chainSyncIn blockFetchIn, Praos chainSyncOut blockFetchOut)

type PraosTrace = [(Time, PraosEvent)]

data PraosEvent
  = -- | Declare the nodes and links
    PraosEventSetup
      !WorldShape
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    PraosEventNode (LabelNode PraosNodeEvent)
  | -- | An event on a tcp link between two nodes
    PraosChainSyncEventTcp (LabelLink (TcpEvent ChainSyncMessage))
  | -- | An event on a tcp link between two nodes
    PraosBlockFetchEventTcp (LabelLink (TcpEvent BlockFetchMessage))
  deriving (Show)

data PraosNodeEvent = PraosNodeEvent
  deriving (Show)

exampleTrace1 :: PraosTrace
exampleTrace1 = traceRelayLink1 $ mkTcpConnProps 0.1 1000000

traceRelayLink1 ::
  TcpConnProps ->
  PraosTrace
traceRelayLink1 tcpprops =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        PraosEventSetup
          WorldShape
            { worldDimensions = (500, 500)
            , worldIsCylinder = False
            }
          ( Map.fromList
              [ (nodeA, Point 50 100)
              , (nodeB, Point 450 100)
              ]
          )
          ( Set.fromList
              [(nodeA, nodeB), (nodeB, nodeA)]
          )
      let chainA = mkChainSimple $ replicate 10 (BlockBody $ BS.replicate 100 0)
      let chainB = Genesis
      (cspA, cscB) <- newConnectionTCP (chainSyncLinkTracer nodeA nodeB) tcpprops
      (cscA, cspB) <- newConnectionTCP (chainSyncLinkTracer nodeA nodeB) tcpprops
      (bfpA, bfcB) <- newConnectionTCP (blockFetchLinkTracer nodeA nodeB) tcpprops
      (bfcA, bfpB) <- newConnectionTCP (blockFetchLinkTracer nodeA nodeB) tcpprops
      concurrently_
        (runPraosNode chainA [Praos cspA bfpA] [Praos cscA bfcA])
        (runPraosNode chainB [Praos cspB bfpB] [Praos cscB bfcB])
      return ()
 where
  (nodeA, nodeB) = (NodeId 0, NodeId 1)

  tracer :: Tracer (IOSim s) PraosEvent
  tracer = simTracer

  chainSyncLinkTracer ::
    NodeId ->
    NodeId ->
    Tracer (IOSim s) (LabelTcpDir (TcpEvent ChainSyncMessage))
  chainSyncLinkTracer nfrom nto =
    contramap (PraosChainSyncEventTcp . labelDirToLabelLink nfrom nto) tracer

  blockFetchLinkTracer ::
    NodeId ->
    NodeId ->
    Tracer (IOSim s) (LabelTcpDir (TcpEvent BlockFetchMessage))
  blockFetchLinkTracer nfrom nto =
    contramap (PraosBlockFetchEventTcp . labelDirToLabelLink nfrom nto) tracer
