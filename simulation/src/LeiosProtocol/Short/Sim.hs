{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LeiosProtocol.Short.Sim where

import ChanMux
import ChanTCP
import Control.Monad.Class.MonadAsync (
  MonadAsync (async, wait),
 )
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- import PraosProtocol.Common hiding (Point)
import LeiosProtocol.Common hiding (Point)
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import PraosProtocol.Common (defaultPraosConfig)
import PraosProtocol.Common.Chain (Chain (..))
import SimTCPLinks
import SimTypes
import System.Random (mkStdGen)

type LeiosTrace = [(Time, LeiosEvent)]

data LeiosEvent
  = -- | Declare the nodes and links
    LeiosEventSetup
      !WorldShape
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    LeiosEventNode (LabelNode LeiosNodeEvent)
  | -- | An event on a tcp link between two nodes
    LeiosEventTcp (LabelLink (TcpEvent LeiosMessage))
  deriving (Show)

exampleTrace1 :: LeiosTrace
exampleTrace1 = traceRelayLink1 $ mkTcpConnProps 0.1 1000000

traceRelayLink1 ::
  TcpConnProps ->
  LeiosTrace
traceRelayLink1 tcpprops =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        LeiosEventSetup
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
      praosConfig <- defaultPraosConfig
      let leiosConfig =
            LeiosConfig
              { praos = praosConfig
              , sliceLength = 7
              , -- \^ measured in slots, also stage length in Short leios.
                inputBlockFrequencyPerSlot = 5
              , -- \^ expected InputBlock generation rate per slot.
                endorseBlockFrequencyPerStage = 3
              , -- \^ expected EndorseBlock generation rate per stage, at most one per _node_ in each (pipeline, stage).
                activeVotingStageLength = 1
              , -- \^ prefix of the voting stage where new votes are generated, <= sliceLength.
                votingFrequencyPerStage = 20
              , votesForCertificate = 10
              , sizes =
                  SizesConfig
                    { producerId = 4
                    , vrfProof = 32
                    , signature_ = 32
                    , reference = 32
                    , voteCrypto = 64
                    , certificate = const (50 * 1024)
                    }
              , delays =
                  LeiosDelays
                    { inputBlockHeaderValidation = const 0.005
                    , -- \^ vrf and signature
                      inputBlockValidation = const 0.1
                    , -- \^ hash matching and payload validation (incl. tx scripts)
                      endorseBlockValidation = const 0.005
                    , voteMsgValidation = const 0.005
                    , certificateCreation = const 0.050
                    }
              }
      let leiosNodeConfig nodeId@(NodeId i) =
            LeiosNodeConfig
              { leios = leiosConfig
              , rankingBlockFrequencyPerSlot = 0.2
              , stake = StakeFraction 0.5
              , rng = mkStdGen i
              , -- \^ for block generation
                baseChain = Genesis
              , rankingBlockPayload = 0
              , -- \^ overall size of txs to include in RBs
                inputBlockPayload = 96 * 1024
              , -- \^ overall size of txs to include in IBs
                processingQueueBound = 100
              , ..
              }

      (pA, cB) <- newConnectionBundleTCP (leiosTracer nodeA nodeB) tcpprops
      (cA, pB) <- newConnectionBundleTCP (leiosTracer nodeA nodeB) tcpprops
      threads <-
        (++)
          <$> (leiosNode (nodeTracer nodeA) (leiosNodeConfig nodeA) [pA] [cA])
          <*> (leiosNode (nodeTracer nodeB) (leiosNodeConfig nodeB) [pB] [cB])
      mapM_ wait =<< mapM async threads
      return ()
 where
  (nodeA, nodeB) = (NodeId 0, NodeId 1)

  tracer :: Tracer (IOSim s) LeiosEvent
  tracer = simTracer

  nodeTracer :: NodeId -> Tracer (IOSim s) LeiosNodeEvent
  nodeTracer n =
    contramap (LeiosEventNode . LabelNode n) tracer

  leiosTracer ::
    NodeId ->
    NodeId ->
    Tracer (IOSim s) (LabelTcpDir (TcpEvent LeiosMessage))
  leiosTracer nfrom nto =
    contramap (LeiosEventTcp . labelDirToLabelLink nfrom nto) tracer
