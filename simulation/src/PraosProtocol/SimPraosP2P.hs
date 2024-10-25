{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module PraosProtocol.SimPraosP2P where

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

import ChanMux (newConnectionBundleTCP)
import ChanTCP
import P2P (P2PTopography (..))
import PraosProtocol.BlockGeneration (slotConfigFromNow)
import PraosProtocol.Common
import PraosProtocol.PraosNode
import PraosProtocol.SimPraos
import SimTCPLinks (labelDirToLabelLink, selectTimedEvents, simTracer)
import SimTypes

tracePraosP2P ::
  StdGen ->
  P2PTopography ->
  (DiffTime -> TcpConnProps) ->
  (SlotConfig -> NodeId -> StdGen -> PraosNodeConfig) ->
  PraosTrace
tracePraosP2P
  rng0
  P2PTopography
    { p2pNodes
    , p2pLinks
    , p2pWorldShape
    }
  tcpprops
  praosConfig =
    selectTimedEvents $
      runSimTrace $ do
        slotConfig <- slotConfigFromNow
        traceWith tracer $
          PraosEventSetup
            p2pWorldShape
            p2pNodes
            (Map.keysSet p2pLinks)
        tcplinks <-
          sequence
            [ do
              (inChan, outChan) <-
                newConnectionBundleTCP @Praos
                  (linkTracer na nb)
                  (tcpprops (realToFrac latency))
              return ((na, nb), (inChan, outChan))
            | ((na, nb), latency) <- Map.toList p2pLinks
            ]
        let tcplinksInChan =
              Map.fromListWith
                (++)
                [ (nfrom, [inChan])
                | ((nfrom, _nto), (inChan, _outChan)) <- tcplinks
                ]
            tcplinksOutChan =
              Map.fromListWith
                (++)
                [ (nto, [outChan])
                | ((_nfrom, nto), (_inChan, outChan)) <- tcplinks
                ]
        -- Note that the incomming edges are the output ends of the
        -- channels and vice versa. That's why it looks backwards.
        runConcurrently $
          sequenceA_
            [ Concurrently $
              praosNode
                (nodeTracer nid)
                (praosConfig slotConfig nid rng)
                (Map.findWithDefault [] nid tcplinksInChan)
                (Map.findWithDefault [] nid tcplinksOutChan)
            | (nid, rng) <-
                zip
                  (Map.keys p2pNodes)
                  (unfoldr (Just . split) rng0)
            ]
   where
    tracer :: Tracer (IOSim s) PraosEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) PraosNodeEvent
    nodeTracer n =
      contramap (PraosEventNode . LabelNode n) tracer

    linkTracer ::
      NodeId ->
      NodeId ->
      Tracer
        (IOSim s)
        (LabelTcpDir (TcpEvent PraosMessage))
    linkTracer nfrom nto =
      contramap (PraosEventTcp . labelDirToLabelLink nfrom nto) tracer
