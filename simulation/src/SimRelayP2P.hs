{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SimRelayP2P where

import Control.Monad.Class.MonadAsync (
  Concurrently (Concurrently, runConcurrently),
 )
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import Data.Foldable (sequenceA_)
import Data.List (unfoldr)
import qualified Data.Map.Strict as Map
import System.Random (StdGen, split)
import TimeCompat

import Chan
import Chan.TCP (newConnectionTCP)
import P2P
import SimRelay
import SimTCPLinks (labelDirToLabelLink, selectTimedEvents, simTracer)
import SimTypes
import Topology

traceRelayP2P ::
  StdGen ->
  P2PNetwork ->
  (DiffTime -> Maybe Bytes -> TcpConnProps) ->
  (StdGen -> RelayNodeConfig) ->
  RelaySimTrace
traceRelayP2P
  rng0
  P2PNetwork
    { p2pNodes
    , p2pLinks
    , p2pWorld
    }
  tcpprops
  relayConfig =
    selectTimedEvents $
      runSimTrace $ do
        traceWith tracer $
          RelaySimEventSetup
            p2pWorld
            p2pNodes
            (Map.keysSet p2pLinks)
        (chansToDownstream :<- chansToUpstream) <- traverseLinks p2pLinks $ \na nb (latency, bw) ->
          newConnectionTCP
            (linkTracer na nb)
            (tcpprops (secondsToDiffTime latency) bw)
        runConcurrently $
          sequenceA_
            [ Concurrently $
                relayNode
                  (nodeTracer nid)
                  (relayConfig rng)
                  (Map.findWithDefault [] nid chansToDownstream)
                  (Map.findWithDefault [] nid chansToUpstream)
            | (nid, rng) <-
                zip
                  (Map.keys p2pNodes)
                  (unfoldr (Just . split) rng0)
            ]
   where
    tracer :: Tracer (IOSim s) RelaySimEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) (RelayNodeEvent TestBlock)
    nodeTracer n =
      contramap (RelaySimEventNode . LabelNode n) tracer

    linkTracer ::
      NodeId ->
      NodeId ->
      Tracer
        (IOSim s)
        (LabelTcpDir (TcpEvent TestBlockRelayMessage))
    linkTracer nfrom nto =
      contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer
