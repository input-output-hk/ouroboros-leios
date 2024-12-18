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
import qualified Data.Map.Strict as M
import qualified Data.Map.Strict as Map
import LeiosProtocol.Common
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import LeiosProtocol.Short.Sim
import P2P (P2PTopography (..))
import SimTCPLinks (labelDirToLabelLink, mkTcpConnProps, selectTimedEvents, simTracer)
import SimTypes
import System.Random (StdGen, split)

traceLeiosP2P ::
  StdGen ->
  P2PTopography ->
  (DiffTime -> TcpConnProps) ->
  (SlotConfig -> NodeId -> StdGen -> LeiosNodeConfig) ->
  LeiosTrace
traceLeiosP2P
  rng0
  P2PTopography
    { p2pNodes
    , p2pLinks
    , p2pWorldShape
    }
  tcpprops
  leiosNodeConfig =
    selectTimedEvents $
      runSimTrace $ do
        slotConfig <- slotConfigFromNow
        traceWith tracer $
          LeiosEventSetup
            p2pWorldShape
            p2pNodes
            (Map.keysSet p2pLinks)
        tcplinks <-
          sequence
            [ do
              (inChan, outChan) <-
                newConnectionBundleTCP @Leios
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
        forever $ threadDelaySI 1000
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

exampleTrace2 :: StdGen -> Int -> P2PTopography -> LeiosTrace
exampleTrace2 rng0 sliceLength p2pTopography@P2PTopography{..} =
  traceLeiosP2P
    rng0
    p2pTopography
    (\latency -> mkTcpConnProps latency (kilobytes 1000))
    leiosNodeConfig
 where
  p2pNumNodes = fromIntegral (M.size p2pNodes)
  leiosNodeConfig slotConfig nodeId rng =
    LeiosNodeConfig
      { stake = StakeFraction $ 1 / p2pNumNodes
      , baseChain = Genesis
      , leios
      , rankingBlockFrequencyPerSlot = 1 / fromIntegral leios.sliceLength
      , rankingBlockPayload = 0
      , inputBlockPayload = kilobytes 96
      , processingQueueBound = 100
      , nodeId
      , rng
      }
   where
    leios = exampleLeiosConfig sliceLength slotConfig

exampleLeiosConfig :: Int -> SlotConfig -> LeiosConfig
exampleLeiosConfig sliceLength slotConfig = leios
 where
  -- TODO: review voting numbers, these might not make sense.
  leios =
    LeiosConfig
      { praos
      , sliceLength = sliceLength -- matching the interval between RBs
      , inputBlockFrequencyPerSlot = 5
      , endorseBlockFrequencyPerStage = 1.5
      , activeVotingStageLength = 1
      , votingFrequencyPerStage = 500
      , votesForCertificate = 150
      , sizes
      , delays
      }
  -- TODO: realistic sizes
  sizes =
    SizesConfig
      { producerId = 4
      , vrfProof = 32
      , signature_ = 32
      , reference = 32
      , voteCrypto = 64
      , certificate = const (50 * 1024)
      }
  delays =
    LeiosDelays
      { inputBlockHeaderValidation = const 0.005
      , inputBlockValidation = const 0.1
      , endorseBlockValidation = const 0.005
      , voteMsgValidation = const 0.005
      , certificateCreation = const 0.050
      }

  praos =
    PraosConfig
      { slotConfig
      , blockValidationDelay = const 0.1 -- 100ms --TODO: should depend on certificate/payload
      , headerValidationDelay = const 0.005 -- 5ms
      }
