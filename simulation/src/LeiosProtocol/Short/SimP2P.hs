{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module LeiosProtocol.Short.SimP2P where

import Chan (ConnectionConfig, newConnectionBundle)
import Chan.TCP
import Control.Monad (forever)
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (Contravariant (..), Tracer, traceWith)
import Data.List (unfoldr)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import LeiosProtocol.Common
import qualified LeiosProtocol.Config as OnDisk
import LeiosProtocol.Short (LeiosConfig (..), convertConfig)
import LeiosProtocol.Short.Node
import LeiosProtocol.Short.Sim
import P2P
import SimTCPLinks (labelDirToLabelLink, selectTimedEvents, simTracer)
import SimTypes
import System.Random (StdGen, split)
import Topology (P2PNetwork (..))
import qualified Topology

traceLeiosP2P ::
  StdGen ->
  P2PNetwork ->
  (DiffTime -> Maybe Bytes -> ConnectionConfig) ->
  (SlotConfig -> NodeId -> StdGen -> LeiosNodeConfig) ->
  LeiosTrace
traceLeiosP2P
  rng0
  P2PNetwork
    { p2pNodes
    , p2pNodeStakes
    , p2pLinks
    , p2pWorld
    }
  tcpprops
  leiosNodeConfig =
    selectTimedEvents $
      runSimTrace $ do
        slotConfig <- slotConfigFromNow
        traceWith tracer $
          LeiosEventSetup
            p2pWorld
            p2pNodes
            p2pNodeStakes
            (Map.keysSet p2pLinks)

        (chansToDownstream :<- chansToUpstream) <-
          traverseLinks p2pLinks $ \na nb (latency, bandwidth) ->
            newConnectionBundle @Leios
              (linkTracer na nb)
              (tcpprops (realToFrac latency) bandwidth)
        -- Nested children threads are slow with IOSim, this impl forks them all as direct children.
        mapM_
          (\m -> mapM_ forkIO =<< m)
          [ leiosNode
            (nodeTracer nid)
            (leiosNodeConfig slotConfig nid rng)
            (Map.findWithDefault [] nid chansToDownstream)
            (Map.findWithDefault [] nid chansToUpstream)
          | (nid, rng) <-
              zip
                (Map.keys p2pNodes)
                (unfoldr (Just . split) rng0)
          ]
        forever $ threadDelay 1000
   where
    tracer :: Tracer (IOSim s) LeiosEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) LeiosNodeEvent
    nodeTracer n =
      contramap (LeiosEventNode . LabelNode n) tracer

    linkTracer ::
      NodeId ->
      NodeId ->
      Tracer
        (IOSim s)
        (LabelTcpDir (TcpEvent LeiosMessage))
    linkTracer nfrom nto =
      contramap (LeiosEventTcp . labelDirToLabelLink nfrom nto) tracer

exampleTrace2 :: StdGen -> OnDisk.Config -> P2PNetwork -> Bool -> LeiosTrace
exampleTrace2 rng = exampleTrace2' rng . convertConfig

exampleTrace2' :: StdGen -> LeiosConfig -> P2PNetwork -> Bool -> LeiosTrace
exampleTrace2' rng0 leios@LeiosConfig{praos = PraosConfig{configureConnection}} p2pTopography@P2PNetwork{..} conformanceEvents =
  traceLeiosP2P
    rng0
    p2pTopography
    configureConnection
    leiosNodeConfig
 where
  leiosNodeConfig slotConfig nodeId rng =
    LeiosNodeConfig
      { stake = fromMaybe undefined $ Map.lookup nodeId p2pNodeStakes
      , baseChain = Genesis
      , slotConfig
      , leios
      , processingQueueBound = defaultQueueBound processingCores
      , processingCores
      , nodeId
      , rng
      , blockGeneration = case Map.lookup nodeId =<< p2pAdversaries of
          Nothing -> Honest
          Just Topology.UnboundedIbs{..} ->
            UnboundedIbs
              { startingAtSlot = SlotNo $ fromIntegral startingAtSlot
              , slotOfGeneratedIbs = SlotNo $ fromIntegral slotOfGeneratedIbs
              , ibsPerSlot = fromIntegral ibsPerSlot
              }
      , conformanceEvents
      }
   where
    processingCores = fromMaybe undefined $ Map.lookup nodeId p2pNodeCores
