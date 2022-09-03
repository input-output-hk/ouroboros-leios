{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module SimRelayP2P where

import           Data.List
import           Data.Foldable
import qualified Data.Map.Strict as Map

import Control.Monad.Class.MonadTime
import Control.Monad.Class.MonadAsync
import Control.Tracer as Tracer

import Control.Monad.IOSim as IOSim

import System.Random (StdGen, split)

import ChanTCP
import SimTCPLinks (LabelNode(..), NodeId(..),
                    simTracer, labelDirToLabelLink, selectTimedEvents)
import P2P
import SimRelay


traceRelayP2P :: StdGen
              -> P2PTopographyCharacteristics
              -> (DiffTime -> TcpConnProps)
              -> (StdGen -> RelayNodeConfig)
              -> RelaySimTrace
traceRelayP2P rng0 p2pTopographyCharacteristics tcpprops relayConfig =
    selectTimedEvents $
    runSimTrace $ do
      let P2PTopography {p2pNodes, p2pLinks} =
            genArbitraryP2PTopography p2pTopographyCharacteristics rng0
      traceWith tracer $
        RelaySimEventSetup
          [ (nid, (round x, round y))
          | (nid, (x,y)) <- Map.toList p2pNodes ]
          (Map.keys p2pLinks)
      tcplinks <-
        sequence
          [ do (inChan, outChan) <- newConnectionTCP (linkTracer na nb)
                                                     (tcpprops latency)
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

