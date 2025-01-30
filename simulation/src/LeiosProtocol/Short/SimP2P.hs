{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module LeiosProtocol.Short.SimP2P where

import ChanMux (newConnectionBundleTCP)
import ChanTCP
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
import Data.Maybe (fromMaybe)
import LeiosProtocol.Common
import qualified LeiosProtocol.Config as OnDisk
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import LeiosProtocol.Short.Sim
import SimTCPLinks (labelDirToLabelLink, mkTcpConnProps, selectTimedEvents, simTracer)
import SimTypes
import System.Random (StdGen, split)
import Topology (P2PNetwork (..))

traceLeiosP2P ::
  StdGen ->
  P2PNetwork ->
  (DiffTime -> Maybe Bytes -> TcpConnProps) ->
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
        tcplinks <-
          sequence
            [ do
              (inChan, outChan) <-
                newConnectionBundleTCP @Leios
                  (linkTracer na nb)
                  (tcpprops (realToFrac latency) bandwidth)
              return ((na, nb), (inChan, outChan))
            | ((na, nb), (latency, bandwidth)) <- Map.toList p2pLinks
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

        -- Nested children threads are slow with IOSim, this impl forks them all as direct children.
        mapM_
          (\m -> mapM_ forkIO =<< m)
          [ leiosNode
            (nodeTracer nid)
            (leiosNodeConfig slotConfig nid rng)
            (Map.findWithDefault [] nid tcplinksInChan)
            (Map.findWithDefault [] nid tcplinksOutChan)
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

exampleTrace2 :: StdGen -> OnDisk.Config -> P2PNetwork -> LeiosTrace
exampleTrace2 rng = exampleTrace2' rng . convertConfig

exampleTrace2' :: StdGen -> LeiosConfig -> P2PNetwork -> LeiosTrace
exampleTrace2' rng0 leios p2pTopography@P2PNetwork{..} =
  traceLeiosP2P
    rng0
    p2pTopography
    (\l b -> mkTcpConnProps l (fromMaybe (error "Unlimited bandwidth: TBD") b))
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
      }
   where
    processingCores = fromMaybe undefined $ Map.lookup nodeId p2pNodeCores
