{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module SimRelayP2P where

import           Data.List
import           Data.Foldable
import qualified Data.Map.Strict as Map

import Control.Monad.Class.MonadTime.SI
import Control.Monad.Class.MonadAsync
import Control.Tracer as Tracer

import Control.Monad.IOSim as IOSim

import System.Random (StdGen, split)

import ChanTCP
import SimTypes
import SimTCPLinks (simTracer, labelDirToLabelLink, selectTimedEvents)
import P2P (P2PTopography(..))
import SimRelay


traceRelayP2P :: StdGen
              -> P2PTopography
              -> (DiffTime -> TcpConnProps)
              -> (StdGen -> RelayNodeConfig)
              -> RelaySimTrace
traceRelayP2P rng0 P2PTopography {
                     p2pNodes,
                     p2pLinks,
                     p2pWorldShape
                   }
              tcpprops relayConfig =
    selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        RelaySimEventSetup
          p2pWorldShape
          p2pNodes
          (Map.keysSet p2pLinks)
      tcplinks <-
        sequence
          [ do (inChan, outChan) <- newConnectionTCP
                                      (linkTracer na nb)
                                      (tcpprops (realToFrac latency))
               return ((na, nb), (inChan, outChan))
          | ((na, nb), latency) <- Map.toList p2pLinks ]
      let tcplinksInChan =
            Map.fromListWith (++)
              [ (nfrom, [inChan])
              | ((nfrom, _nto), (inChan, _outChan)) <- tcplinks ]
          tcplinksOutChan =
            Map.fromListWith (++)
              [ (nto, [outChan])
              | ((_nfrom, nto), (_inChan, outChan)) <- tcplinks ]
          -- Note that the incomming edges are the output ends of the
          -- channels and vice versa. That's why it looks backwards.
      runConcurrently $
        sequenceA_
          [ Concurrently $
              relayNode
                (nodeTracer nid)
                (relayConfig rng)
                (Map.findWithDefault [] nid tcplinksOutChan)
                (Map.findWithDefault [] nid tcplinksInChan)
          | (nid, rng) <- zip (Map.keys p2pNodes)
                              (unfoldr (Just . split) rng0)
          ]
  where
    tracer :: Tracer (IOSim s) RelaySimEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) (RelayNodeEvent TestBlock)
    nodeTracer n =
      contramap (RelaySimEventNode . LabelNode n) tracer

    linkTracer :: NodeId -> NodeId
               -> Tracer (IOSim s)
                         (LabelTcpDir (TcpEvent TestBlockRelayMessage))
    linkTracer nfrom nto =
      contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer

