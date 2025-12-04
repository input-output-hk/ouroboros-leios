{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module PraosProtocol.SimPraosP2P where

import Chan (ConnectionConfig, LabelTcpDir, TcpEvent, newConnectionBundle)
import Control.Monad (forever)
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import Data.List (unfoldr)
import qualified Data.Map.Strict as Map
import P2P
import PraosProtocol.Common
import PraosProtocol.PraosNode
import PraosProtocol.SimPraos
import SimTCPLinks (labelDirToLabelLink, selectTimedEvents, simTracer)
import SimTypes
import System.Random (StdGen, split)
import Topology

tracePraosP2P ::
  StdGen ->
  P2PNetwork ->
  (DiffTime -> Maybe Bytes -> ConnectionConfig) ->
  (SlotConfig -> NodeId -> StdGen -> PraosNodeConfig) ->
  PraosTrace
tracePraosP2P
  rng0
  P2PNetwork
    { p2pNodes
    , p2pLinks
    , p2pWorld
    }
  configureConnection
  praosConfig =
    selectTimedEvents $
      runSimTrace $ do
        slotConfig <- slotConfigFromNow
        traceWith tracer $
          PraosEventSetup
            p2pWorld
            p2pNodes
            (Map.keysSet p2pLinks)

        (chansToDownstream :<- chansToUpstream) <-
          traverseLinks p2pLinks $ \na nb (latency, bw) ->
            newConnectionBundle @(Praos BlockBody)
              (linkTracer na nb)
              (configureConnection (realToFrac latency) bw)

        -- Nested children threads are slow with IOSim, this impl forks them all as direct children.
        mapM_
          (\m -> mapM_ forkIO =<< m)
          [ praosNode
              (nodeTracer nid)
              (praosConfig slotConfig nid rng)
              (Map.findWithDefault [] nid chansToDownstream)
              (Map.findWithDefault [] nid chansToUpstream)
          | (nid, rng) <-
              zip
                (Map.keys p2pNodes)
                (unfoldr (Just . split) rng0)
          ]
        forever $ threadDelay 1000
   where
    tracer :: Tracer (IOSim s) PraosEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) (PraosNodeEvent BlockBody)
    nodeTracer n =
      contramap (PraosEventNode . LabelNode n) tracer

    linkTracer ::
      NodeId ->
      NodeId ->
      Tracer
        (IOSim s)
        (LabelTcpDir (TcpEvent (PraosMessage BlockBody)))
    linkTracer nfrom nto =
      contramap (PraosEventTcp . labelDirToLabelLink nfrom nto) tracer
