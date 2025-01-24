{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module PraosProtocol.ExamplesPraosP2P where

import ChanDriver
import ChanTCP
import Control.Monad
import Data.Aeson
import Data.Aeson.Types
import qualified Data.ByteString.Char8 as BS8
import Data.Coerce (coerce)
import Data.Fixed
import Data.Functor.Contravariant (Contravariant (contramap))
import qualified Data.IntMap.Strict as IMap
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import GHC.Generics (Generic)
import qualified LeiosProtocol.Config as OnDisk
import Network.TypedProtocol
import P2P (P2PTopography, P2PTopographyCharacteristics (..), genArbitraryP2PTopography, p2pNodes)
import PraosProtocol.BlockFetch
import PraosProtocol.BlockGeneration (PacketGenerationPattern (..))
import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain
import PraosProtocol.PraosNode
import PraosProtocol.SimPraos
import PraosProtocol.SimPraosP2P
import PraosProtocol.VizSimPraos (ChainsMap, DiffusionLatencyMap, PraosVizConfig' (blockFetchMessageColor), accumChains, accumDiffusionLatency, examplesPraosSimVizConfig, praosSimVizModel)
import PraosProtocol.VizSimPraosP2P
import Sample
import SimTCPLinks (mkTcpConnProps)
import SimTypes
import System.FilePath
import System.Random (StdGen, mkStdGen)
import qualified Topology as P2P
import Viz

example1 :: StdGen -> PraosConfig BlockBody -> P2P.P2PNetwork -> Visualization
example1 _rng0 _cfg _p2pNetwork@P2P.P2PNetwork{p2pLinks, p2pNodeStakes}
  | not $ null [() | (_, Nothing) <- Map.elems p2pLinks] =
      error "Only finite bandwidth for this vizualization"
  | length (List.group $ Map.elems p2pNodeStakes) /= 1 =
      error "Only uniform stake supported for this vizualization"
example1 rng0 cfg p2pNetwork =
  Viz (praosSimVizModel (example1Trace rng0 cfg p2pNetwork)) $
    LayoutAbove
      [ layoutLabelTime
      , LayoutBeside
          [ LayoutReqSize 1200 1000 $
              Layout $
                praosP2PSimVizRender config
          , LayoutBeside
              [ LayoutAbove
                  [ LayoutReqSize 350 300 $
                      Layout $
                        chartDiffusionLatency config
                  , LayoutReqSize 350 300 $
                      Layout $
                        chartDiffusionImperfection
                          (P2P.networkToTopology p2pNetwork)
                          0.1
                          (96 / 1000)
                          config
                  ]
              , LayoutAbove
                  [ LayoutReqSize 350 300 $
                      Layout chartBandwidth
                  , LayoutReqSize 350 300 $
                      Layout chartLinkUtilisation
                  ]
              ]
          ]
      ]

data DiffusionEntry = DiffusionEntry
  { hash :: Int
  , node_id :: Int
  , created :: DiffTime
  , arrivals :: [DiffTime]
  }
  deriving (Generic, ToJSON, FromJSON)

data LatencyPerStake = LatencyPerStake
  { hash :: Int
  , latencies :: [(Maybe DiffTime, Double)]
  }
  deriving (Generic, ToJSON, FromJSON)

data DiffusionData = DiffusionData
  { topography_details :: P2PTopography
  , entries :: [DiffusionEntry]
  , latency_per_stake :: [LatencyPerStake]
  -- ^ adoption latency, counted from slot start.
  , stable_chain_hashes :: [Int]
  , average_latencies :: Map.Map Double DiffTime
  }
  deriving (Generic, ToJSON, FromJSON)

diffusionEntryToLatencyPerStake :: Int -> DiffusionEntry -> LatencyPerStake
diffusionEntryToLatencyPerStake nnodes DiffusionEntry{..} =
  LatencyPerStake
    { hash
    , latencies = bin $ diffusionLatencyPerStakeFraction nnodes slotStart (map Time arrivals)
    }
 where
  slotStart = Time $ fromIntegral @Integer $ floor created
  bins = [0.50, 0.8, 0.9, 0.92, 0.94, 0.96, 0.98, 1]
  bin xs = map (\b -> (,b) $ fst <$> listToMaybe (dropWhile (\(_, x) -> x < b) xs)) bins

data DiffusionLatencyState = DiffusionLatencyState
  { chains :: !ChainsMap
  , diffusions :: !DiffusionLatencyMap
  , fetchRequests :: !(Map.Map NodeId (Map.Map (HeaderHash (Block BlockBody)) [DiffTime]))
  , receivedBodies :: !(Map.Map NodeId (Map.Map (HeaderHash (Block BlockBody)) [DiffTime]))
  , blocks :: !(Blocks BlockBody)
  }

diffusionSampleModel :: P2PTopography -> FilePath -> SampleModel PraosEvent DiffusionLatencyState
diffusionSampleModel p2pTopography fp = SampleModel initState accum render
 where
  initState = DiffusionLatencyState IMap.empty Map.empty Map.empty Map.empty Map.empty
  accum t e DiffusionLatencyState{..} =
    DiffusionLatencyState
      { chains = accumChains t e chains
      , diffusions = accumDiffusionLatency t e diffusions
      , fetchRequests = accumFetchRequests blocks t e fetchRequests
      , receivedBodies = accumReceived t e receivedBodies
      , blocks = accumBlocks e blocks
      }
  nnodes = Map.size $ p2pNodes p2pTopography
  render DiffusionLatencyState{..} = do
    let stable_chain = fromMaybe Genesis $ do
          guard $ not $ IMap.null chains
          pure $ List.foldl1' aux (IMap.elems chains)
        aux c1 c2 = fromMaybe Genesis $ do
          p <- Chain.intersectChains c1 c2
          Chain.rollback p c1
    let stable_chain_hashes = coerce $ map blockHash $ Chain.toNewestFirst stable_chain
    let entries =
          [ DiffusionEntry
            { hash = coerce hash'
            , node_id = coerce i
            , created = coerce t
            , arrivals = coerce ts
            }
          | (hash', (_, i, t, ts)) <- Map.toList diffusions
          ]
    let latency_per_stake = map (diffusionEntryToLatencyPerStake nnodes) entries
    let avg ts = sum ts / fromIntegral (length ts)
    let average_latencies =
          Map.map avg $
            Map.fromListWith
              (++)
              [ (p, [d])
              | l <- latency_per_stake
              , (Just d, p) <- l.latencies
              ]
    let timesDiff [t0] [t1] = (realToFrac t1 - realToFrac t0 :: Pico)
        timesDiff _ _ = undefined
    let durations =
          Map.intersectionWith
            ( Map.intersectionWith timesDiff
            )
            fetchRequests
            receivedBodies
    let average_block_fetch_duration =
          avg $
            concatMap Map.elems $
              Map.elems $
                durations ::
            Pico
    let diffusionData =
          DiffusionData
            { topography_details = p2pTopography
            , entries
            , latency_per_stake
            , stable_chain_hashes
            , average_latencies
            }

    encodeFile fp diffusionData
    putStrLn $ "Diffusion data written to " ++ fp
    let arrived98 = unzip [(l.hash, d) | l <- diffusionData.latency_per_stake, (Just d, p) <- l.latencies, p == 0.98]
    let missing = filter (not . (`elem` fst arrived98)) diffusionData.stable_chain_hashes
    putStrLn $ "Number of blocks that reached 98% stake: " ++ show (length $ fst arrived98)
    putStrLn $ "with a maximum diffusion latency: " ++ show (maximum $ 0 : snd arrived98)
    putStrLn $ "Blocks in longest common prefix that did not reach 98% stake: " ++ show missing
    putStrLn $ "Average latencies by percentile"
    putStrLn $ unlines $ map show $ Map.toList average_latencies
    putStrLn $ "Average block fetch duration: " ++ show average_block_fetch_duration

accumFetchRequests :: Map.Map ConcreteHeaderHash (Block BlockBody) -> Time -> PraosEvent -> Map.Map NodeId (Map.Map ConcreteHeaderHash [DiffTime]) -> Map.Map NodeId (Map.Map ConcreteHeaderHash [DiffTime])
accumFetchRequests blocks (Time t) (PraosEventTcp (LabelLink from _to (TcpSendMsg (PraosMessage (Right (ProtocolMessage (SomeMessage (MsgRequestRange start end))))) _ _))) =
  let
    blks = fromMaybe undefined $ resolveRange' blocks start end
   in
    Map.insertWith
      (Map.unionWith (++))
      from
      (Map.fromList $ map (\blk -> (blockHash @(Block BlockBody) blk, [t])) $ blks)
accumFetchRequests _ _ _ = id

accumReceived ::
  Time ->
  PraosEvent ->
  Map.Map NodeId (Map.Map ConcreteHeaderHash [DiffTime]) ->
  Map.Map NodeId (Map.Map ConcreteHeaderHash [DiffTime])
accumReceived (Time t) (PraosEventNode (LabelNode nid (PraosNodeEventReceived block))) =
  let
    blks = [block]
   in
    Map.insertWith
      (Map.unionWith (++))
      nid
      (Map.fromList $ map (\blk -> (blockHash @(Block BlockBody) blk, [t])) $ blks)
accumReceived _ _ = id

accumBlocks :: PraosEvent -> Blocks BlockBody -> Blocks BlockBody
accumBlocks (PraosEventNode (LabelNode _nid (PraosNodeEventGenerate block))) = Map.insert (blockHash block) block
accumBlocks _ = id

accumCPUTasks :: Time -> PraosEvent -> Map.Map NodeId [(DiffTime, CPUTask)] -> Map.Map NodeId [(DiffTime, CPUTask)]
accumCPUTasks (Time t) (PraosEventNode (LabelNode nId (PraosNodeEventCPU task))) = Map.insertWith (++) nId [(t, task)]
accumCPUTasks _ _ = id

convertConfig :: MessageSize body => OnDisk.Config -> PraosConfig body
convertConfig disk = praos
 where
  durationMsToDiffTime (OnDisk.DurationMs d) = secondsToDiffTime $ d / 1000
  praos =
    PraosConfig
      { blockFrequencyPerSlot = disk.rbGenerationProbability
      , headerSize = fromIntegral disk.ibHeadSizeBytes
      , bodySize = \_ -> fromIntegral disk.rbBodyLegacyPraosPayloadAvgSizeBytes
      , bodyMaxSize = fromIntegral disk.rbBodyMaxSizeBytes
      , blockValidationDelay = \(Block _ body) ->
          durationMsToDiffTime $
            disk.rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant
              + disk.rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte * fromIntegral (messageSizeBytes body)
      , headerValidationDelay = const $ durationMsToDiffTime disk.ibHeadValidationCpuTimeMs
      , blockGenerationDelay = \_ ->
          durationMsToDiffTime disk.rbGenerationCpuTimeMs
      }

-- | Diffusion example with 1000 nodes.
example1000Diffusion ::
  StdGen ->
  Maybe OnDisk.Config ->
  P2P.P2PNetwork ->
  -- | when to stop simulation.
  Time ->
  -- | file to write data to.
  FilePath ->
  IO ()
example1000Diffusion rng0 cfg p2pNetwork@P2P.P2PNetwork{p2pNodes, p2pNodeStakes} stop fp
  | length (List.group (Map.elems p2pNodeStakes)) /= 1 = error "Only uniform stake distribution supported for this sim."
  | otherwise =
      runSampleModel traceFile logEvent (diffusionSampleModel (P2P.networkToTopology p2pNetwork) fp) stop $
        trace
 where
  asString x = x :: String
  logEvent (PraosEventNode (LabelNode nid (PraosNodeEventGenerate blk))) =
    Just $
      object ["nid" .= nid, "tag" .= asString "generated", "hash" .= show (coerce @_ @Int (blockHash blk))]
  logEvent (PraosEventNode (LabelNode nid (PraosNodeEventReceived blk))) =
    Just $
      object ["nid" .= nid, "tag" .= asString "received", "hash" .= show (coerce @_ @Int (blockHash blk))]
  logEvent (PraosEventNode (LabelNode nid (PraosNodeEventEnterState blk))) =
    Just $
      object ["nid" .= nid, "tag" .= asString "enterstate", "hash" .= show (coerce @_ @Int (blockHash blk))]
  logEvent (PraosEventNode (LabelNode nid (PraosNodeEventCPU task))) =
    Just $
      object ["nid" .= nid, "tag" .= asString "cpu", "task" .= task]
  logEvent (PraosEventTcp (LabelLink from to (TcpSendMsg msg _ _))) = do
    ps <- logMsg msg
    pure $ object $ ["tag" .= asString "Sent", "sender" .= from, "receipient" .= to] <> ps
  logEvent _ = Nothing
  logMsg :: PraosMessage BlockBody -> Maybe [Pair]
  logMsg ((PraosMessage (Right (ProtocolMessage (SomeMessage (MsgBlock hash _body)))))) =
    Just $ ["id" .= show (coerce @_ @Int hash)]
  logMsg ((PraosMessage _)) = Nothing

  traceFile = dropExtension fp <.> "log"
  blockInterval = 1 / praosConfig.blockFrequencyPerSlot
  praosConfig = maybe defaultPraosConfig convertConfig cfg
  p2pNumNodes = Map.size $ p2pNodes
  trace =
    tracePraosP2P
      rng0
      p2pNetwork
      (\latency -> mkTcpConnProps latency . fromMaybe (error "Only finite bandwidth supported for this sim."))
      ( \slotConfig nid rng ->
          PraosNodeConfig
            { blockGeneration =
                PoissonGenerationPattern
                  rng
                  -- average seconds between blocks:
                  (realToFrac blockInterval * fromIntegral p2pNumNodes)
            , praosConfig
            , blockMarker = BS8.pack $ show nid ++ ": "
            , chain = Genesis
            , slotConfig
            }
      )

example1Trace :: StdGen -> PraosConfig BlockBody -> P2P.P2PNetwork -> PraosTrace
example1Trace rng0 praosConfig p2pNetwork@P2P.P2PNetwork{p2pNodes} =
  tracePraosP2P
    rng0
    p2pNetwork
    (\latency -> mkTcpConnProps latency . fromMaybe undefined)
    ( \slotConfig nid rng ->
        PraosNodeConfig
          { blockGeneration =
              PoissonGenerationPattern
                rng
                -- average seconds between blocks:
                (realToFrac blockInterval * fromIntegral p2pNumNodes)
          , slotConfig
          , praosConfig
          , blockMarker = BS8.pack $ show nid ++ ": "
          , chain = Genesis
          }
    )
 where
  blockInterval = 1 / praosConfig.blockFrequencyPerSlot
  p2pNumNodes = Map.size p2pNodes

example2 :: Visualization
example2 =
  --  slowmoVisualization 0.2 $
  Viz (pairVizModel model1 model2) $
    LayoutAbove
      [ layoutLabel 18 "Flat vs cylindrical world topology"
      , LayoutReqSize 0 40 $
          layoutLabel 10 $
            "Left side is a flat rectangular world.\n"
              ++ "Right is a cylindrical world, i.e. the east and "
              ++ "west edges are connected."
      , layoutLabelTime
      , LayoutBeside
          [ contramap fst
              <$> LayoutAbove
                [ LayoutReqSize 900 600 $
                    Layout $
                      praosP2PSimVizRender config
                , LayoutBeside
                    [ LayoutReqSize 350 300 $
                        Layout $
                          chartDiffusionLatency config
                    , LayoutReqSize 350 300 $
                        Layout
                          chartLinkUtilisation
                    ]
                ]
          , contramap snd
              <$> LayoutAbove
                [ LayoutReqSize 900 600 $
                    Layout $
                      praosP2PSimVizRender config
                , LayoutBeside
                    [ LayoutReqSize 350 300 $
                        Layout $
                          chartDiffusionLatency config
                    , LayoutReqSize 350 300 $
                        Layout
                          chartLinkUtilisation
                    ]
                ]
          ]
      ]
 where
  model1 =
    model
      p2pTopographyCharacteristicsCommon
        { p2pWorld =
            p2pWorld
              { worldShape = Rectangle
              }
        }
  model2 = model p2pTopographyCharacteristicsCommon

  model p2pTopographyCharacteristics =
    praosSimVizModel trace
   where
    trace =
      tracePraosP2P
        rng0
        (P2P.topologyToNetwork (Just (kilobytes 1000)) p2pTopography)
        (\latency -> mkTcpConnProps latency . fromMaybe undefined)
        ( \slotConfig nid rng ->
            PraosNodeConfig
              { blockGeneration =
                  PoissonGenerationPattern
                    rng
                    -- average seconds between blocks:
                    (5 * fromIntegral p2pNumNodes)
              , praosConfig = defaultPraosConfig
              , slotConfig
              , chain = Genesis
              , blockMarker = BS8.pack $ show nid ++ ": "
              }
        )
    p2pTopography =
      genArbitraryP2PTopography p2pTopographyCharacteristics rng0

  rng0 = mkStdGen 4 -- TODO: make a param
  p2pNumNodes = 100
  p2pWorld =
    World
      { worldDimensions = (0.600, 0.300)
      , worldShape = Cylinder
      }
  p2pTopographyCharacteristicsCommon =
    P2PTopographyCharacteristics
      { p2pWorld
      , p2pNumNodes
      , p2pNodeLinksClose = 5
      , p2pNodeLinksRandom = 5
      }

config :: PraosP2PSimVizConfig
config =
  PraosP2PSimVizConfig
    { nodeMessageColor = testNodeMessageColor
    , ptclMessageColor = testPtclMessageColor
    }
 where
  testPtclMessageColor ::
    PraosMessage BlockBody ->
    Maybe (Double, Double, Double)
  testPtclMessageColor msg =
    case msg of
      PraosMessage (Right bmsg@(ProtocolMessage (SomeMessage MsgBlock{}))) ->
        Just (blockFetchMessageColor examplesPraosSimVizConfig bmsg)
      _ -> Nothing

  testNodeMessageColor :: BlockHeader -> (Double, Double, Double)
  testNodeMessageColor = blockHeaderColorAsBody
