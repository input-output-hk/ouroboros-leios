{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Short.DataSimP2P where

import Control.Exception
import Control.Monad
import Data.Aeson
import Data.Aeson.Types
import Data.Bifunctor
import qualified Data.ByteString.Lazy.Char8 as BSL8
import Data.Coerce
import Data.Fixed
import qualified Data.IntMap as IMap
import Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap.Interval as ILMap
import qualified Data.IntervalMap.Strict as ILMap
import Data.List (group, sort, sortOn, uncons)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Diffusion
import GHC.Generics
import LeiosProtocol.Common hiding (Point)
import qualified LeiosProtocol.Config as OnDisk
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import LeiosProtocol.Short.Sim
import LeiosProtocol.Short.SimP2P (exampleTrace2)
import LeiosProtocol.Short.VizSim
import ModelTCP (TcpEvent (TcpSendMsg))
import P2P
import Sample
import SimTypes (Bytes, LabelLink (LabelLink), LabelNode (LabelNode))
import System.FilePath
import System.Random (StdGen)
import Topology

data RawLeiosData = RawLeiosData
  { network :: SomeTopology
  , p2p_network :: P2PNetwork
  , config :: OnDisk.Config
  , ib_diffusion_entries :: [DiffusionEntry InputBlockId]
  , eb_diffusion_entries :: [DiffusionEntry EndorseBlockId]
  , vt_diffusion_entries :: [DiffusionEntry VoteId]
  , rb_diffusion_entries :: [DiffusionEntry Int]
  , stable_chain_hashes :: [Int]
  , cpuUseSegments :: Map.Map NodeId [(Int, Micro)]
  -- ^ cpu usage as a step function: [(cpu#,duration)]
  , transmittedBpsSegments :: !(Map NodeId [(Double, Micro)])
  -- ^ network bandwidth usage as a step function: [(bps,duration)]
  , transmittedMsgsSegments :: Map.Map NodeId [(Int, Micro)]
  -- ^ network msgs sent as a step function: [(msg#,duration)]
  , stop :: Time
  }
  deriving (Generic, ToJSON, FromJSON)

data LeiosData = LeiosData
  { raw :: RawLeiosData
  , ib_diffusion :: DiffusionData InputBlockId
  , eb_diffusion :: DiffusionData EndorseBlockId
  , vt_diffusion :: DiffusionData VoteId
  , rb_diffusion :: DiffusionData Int
  , cpuUseCdfAvg :: ![(Int, Micro)]
  , transmittedBpsCdfAvg :: ![(Double, Micro)]
  , transmittedMsgsCdfAvg :: ![(Int, Micro)]
  }
  deriving (Generic, ToJSON, FromJSON)

data LeiosSimState = LeiosSimState
  { chains :: !ChainsMap
  , rbDiffusionLatency :: !DiffusionLatencyMap
  , ibDiffusionLatency :: !(DiffusionLatencyMap' InputBlockId InputBlockHeader)
  , ebDiffusionLatency :: !(DiffusionLatencyMap' EndorseBlockId EndorseBlock)
  , voteDiffusionLatency :: !(DiffusionLatencyMap' VoteId VoteMsg)
  , nodeCpuUsage :: !(Map NodeId (IntervalMap Micro Int))
  , dataTransmittedPerNode :: !(Map NodeId DataTransmitted)
  }
  deriving (Generic)

accumLeiosSimState ::
  Time ->
  LeiosEvent ->
  LeiosSimState ->
  LeiosSimState
accumLeiosSimState _now (LeiosEventSetup{}) vs =
  vs
accumLeiosSimState _now (LeiosEventNode (LabelNode _nid (PraosNodeEvent (PraosNodeEventNewTip _tip)))) vs =
  vs
accumLeiosSimState now (LeiosEventNode (LabelNode nid (LeiosNodeEvent event blk))) LeiosSimState{..} =
  case blk of
    EventIB x ->
      LeiosSimState
        { ibDiffusionLatency = accumDiffusionLatency' now nid event x.id x.header ibDiffusionLatency
        , ..
        }
    EventEB x ->
      LeiosSimState
        { ebDiffusionLatency = accumDiffusionLatency' now nid event x.id x ebDiffusionLatency
        , ..
        }
    EventVote x ->
      LeiosSimState
        { voteDiffusionLatency = accumDiffusionLatency' now nid event x.id x voteDiffusionLatency
        , ..
        }
accumLeiosSimState now (LeiosEventNode (LabelNode nid (PraosNodeEvent (PraosNodeEventGenerate blk)))) vs =
  vs
    { rbDiffusionLatency =
        assert (not (blockHash blk `Map.member` vs.rbDiffusionLatency)) $
          Map.insert
            (blockHash blk)
            (blockHeader blk, nid, now, [(nid, now)])
            vs.rbDiffusionLatency
    }
accumLeiosSimState _now (LeiosEventNode (LabelNode _nid (PraosNodeEvent (PraosNodeEventReceived _blk)))) vs =
  vs
accumLeiosSimState now (LeiosEventNode (LabelNode nid (PraosNodeEvent (PraosNodeEventEnterState blk)))) vs =
  vs
    { rbDiffusionLatency =
        Map.adjust
          ( \(hdr, nid', created, arrivals) ->
              (hdr, nid', created, (nid, now) : arrivals)
          )
          (blockHash blk)
          vs.rbDiffusionLatency
    }
accumLeiosSimState
  _now
  ( LeiosEventTcp
      ( LabelLink
          nfrom
          _nto
          (TcpSendMsg msg msgforecast _msgforecasts)
        )
    )
  LeiosSimState{..} =
    LeiosSimState
      { dataTransmittedPerNode = Map.alter (Just . accumDataTransmitted msg msgforecast . fromMaybe initDataTransmitted) nfrom dataTransmittedPerNode
      , ..
      }
accumLeiosSimState now (LeiosEventNode (LabelNode nid (LeiosNodeEventCPU task))) LeiosSimState{..} =
  LeiosSimState
    { nodeCpuUsage = accumNodeCpuUsage' @Micro (MkFixed . round . (* 1e6)) now nid task nodeCpuUsage
    , ..
    }
accumLeiosSimState
  _now
  ( LeiosEventNode
      (LabelNode _nodeId (PraosNodeEvent (PraosNodeEventCPU _task)))
    )
  _vs = error "PraosNodeEventCPU should not be generated by leios nodes"

data SimOutputConfig = SimOutputConfig
  { logFile :: Maybe FilePath
  , emitControl :: Bool
  , dataFile :: Maybe FilePath
  , analize :: Bool
  , stop :: Time
  }

rawDataFromState :: OnDisk.Config -> P2PNetwork -> LeiosSimState -> Time -> RawLeiosData
rawDataFromState config p2p_network@P2PNetwork{..} LeiosSimState{..} stop@(Time stop') = RawLeiosData{..}
 where
  ib_diffusion_entries = diffusionEntries ibDiffusionLatency
  eb_diffusion_entries = diffusionEntries ebDiffusionLatency
  vt_diffusion_entries = diffusionEntries voteDiffusionLatency
  rb_diffusion_entries = coerce $ diffusionEntries rbDiffusionLatency
  stable_chain_hashes = coerce $ stableChainHashes chains
  network = p2pNetworkToSomeTopology (fromIntegral $ Map.size p2pNodeStakes * 1000) p2p_network
  cpuUseSegments =
    intervalsToSegments
      (sum . ILMap.elems . fst)
      (realToFrac stop')
      nodeCpuUsage
  transmittedBpsSegments =
    intervalsToSegments
      (\(im, i) -> assert (all (`ILMap.subsumes` i) $ ILMap.keys im) $ msgsTransmittedToBps . fst $ (im, i))
      stop'
      (Map.map (.messagesTransmitted) dataTransmittedPerNode)
  transmittedMsgsSegments =
    intervalsToSegments
      (length . ILMap.elems . fst)
      stop'
      (Map.map (.messagesTransmitted) dataTransmittedPerNode)

maybeAnalizeRawData :: Bool -> RawLeiosData -> LeiosData
maybeAnalizeRawData analize raw@RawLeiosData{..} = LeiosData{..}
 where
  Time stop' = stop
  P2PNetwork{..} = p2p_network
  ib_diffusion = diffusionDataFromEntries analize p2pNodeStakes ib_diffusion_entries
  eb_diffusion = diffusionDataFromEntries analize p2pNodeStakes eb_diffusion_entries
  vt_diffusion = diffusionDataFromEntries analize p2pNodeStakes vt_diffusion_entries
  rb_diffusion = diffusionDataFromEntries analize p2pNodeStakes rb_diffusion_entries
  maybeDoAnalysis :: [a] -> [a]
  maybeDoAnalysis = if analize then id else (const [])
  cpuUseCdfAvg =
    maybeDoAnalysis $
      Map.toAscList $
        segmentsToCdfAvg
          Set.toList
          (realToFrac stop')
          cpuUseSegments
  transmittedBpsCdfAvg =
    maybeDoAnalysis $
      Map.toAscList $
        segmentsToCdfAvg
          (uniformBins 20)
          (realToFrac stop')
          transmittedBpsSegments
  transmittedMsgsCdfAvg =
    maybeDoAnalysis $
      Map.toAscList $
        segmentsToCdfAvg
          Set.toList
          (realToFrac stop')
          transmittedMsgsSegments

exampleSim :: StdGen -> OnDisk.Config -> P2PNetwork -> SimOutputConfig -> IO ()
exampleSim seed cfg p2pNetwork@P2PNetwork{..} SimOutputConfig{..} = do
  case dataFile of
    Just fp ->
      runModel
        SampleModel
          { initState = LeiosSimState IMap.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty
          , accumState = \t e s -> accumLeiosSimState t e s{chains = accumChains t e s.chains}
          , renderState = renderState fp
          }
    Nothing ->
      runModel
        SampleModel
          { initState = ()
          , accumState = \_ _ s -> s
          , renderState = const (return ())
          }
 where
  runModel :: SampleModel LeiosEvent state -> IO ()
  runModel model =
    runSampleModel' logFile (logLeiosEvent p2pNodeNames emitControl) model stop $
      exampleTrace2 seed cfg p2pNetwork
  renderState fp st = do
    let diffusionData = maybeAnalizeRawData analize (rawDataFromState cfg p2pNetwork st stop)
    encodeFile fp diffusionData
    putStrLn $ "Data written to " ++ fp
    when analize $ reportAll diffusionData
  reportAll LeiosData{..} = do
    sequence_ $
      [ uncurry report ("IB", ib_diffusion)
      , uncurry report ("EB", eb_diffusion)
      , uncurry report ("Vote", vt_diffusion)
      , uncurry report ("RB", rb_diffusion)
      ]
  report tag DiffusionData{..} = do
    putStrLn $ tag ++ ": average latencies (from slot start) by percentile"
    putStrLn $ unlines $ map show $ Map.toList average_latencies

coefficientOfVariability :: Floating v => v -> [(v, v)] -> v
coefficientOfVariability total xs = stdDev / mean
 where
  mean = sum (map (uncurry (*)) xs) / total
  stdDev = sqrt $ sum (map (\(x, w) -> ((x - mean) ** 2) * w) xs) / total

uniformBins :: (RealFrac a, Num b) => Integer -> Set.Set a -> [b]
uniformBins n ks = case (fst <$> Set.minView ks, fst <$> Set.maxView ks) of
  (Just (floor -> l), Just u') ->
    let step = (u - l) `div` n :: Integer
        u = ceiling (u' / 10 ^ (m - 2)) * 10 ^ (m - 2)
         where
          m = ceiling @Double @Int $ logBase 10 (realToFrac u')
     in map fromIntegral $
          (++ [u]) . takeWhile (< u) . iterate (+ step) $
            l
  (_, _) -> error "impossible"

-- | Takes a per node Map of interval maps, and some helper functions.
--   Returns
--     * per node, a step function as in-order non-overlapping
--       segments of the input
--
--   Generalized NodeId to `k`.
--
--   We use `d` or `Micro` rather than DiffTime because Double
--   causes spurious interval overlaps.
intervalsToSegments ::
  (Real d, Ord v, Show v) =>
  -- | what value to measure for a given segment interval and map of intersecting ones.
  ((ILMap.IntervalMap Micro a, ILMap.Interval Micro) -> v) ->
  -- | upper bound of the measurement interval (lower bound assumed to be 0), used to normalize interval lengths for the cdf.
  d ->
  Map k (ILMap.IntervalMap d a) ->
  Map k [(v, Micro)]
intervalsToSegments _ _ m | Map.size m == 0 = Map.empty
intervalsToSegments f stop dataPerNode' = segments
 where
  dataPerNode = Map.map (ILMap.fromList . map (first (fmap realToFrac)) . ILMap.toList) dataPerNode'
  segments =
    Map.map
      (map (first f) . segmentILMap (realToFrac stop))
      dataPerNode
  segmentILMap ub im =
    let intervals =
          mapMaybe (fmap fst . uncons) . group . (0 :) . (++ [ub]) . takeWhile (<= ub) $ -- parallel tasks produce duplicates.
            sort $ -- lower bounds are in-order but upper-bounds aren't.
              concatMap (\i -> [ILMap.lowerBound i, ILMap.upperBound i]) $
                ILMap.keys im
     in [ ((ILMap.intersecting im i, i), ILMap.upperBound i - ILMap.lowerBound i)
        | i <-
            [ ILMap.IntervalCO x y
            | (x, y) <- zip intervals (drop 1 intervals)
            ]
        ]

segmentsToCdfAvg ::
  (Ord v, Show v) =>
  -- | function to pick out keys for the cdf from set of segment keys.
  (Set.Set v -> [v]) ->
  -- | upper bound of the measurement interval (lower bound assumed to be 0), used to normalize interval lengths for the cdf.
  Micro ->
  Map k [(v, Micro)] ->
  Map v Micro
segmentsToCdfAvg _ _ m | Map.size m == 0 = Map.empty
segmentsToCdfAvg bins stop segments = avgMaps $ map pmfToCdf $ pmfs
 where
  numNodes = Map.size segments
  pmfs = map (weightedSamplesToPmf stop) . Map.elems $ segments
  -- we sample the cdfs to have the same keys, so we can take take average pointwise.
  sampleCdfs cdfs = map sampleCdf cdfs
   where
    ks = bins $ Set.unions $ map Map.keysSet cdfs
    sampleCdf m = Map.fromList [(k, v) | k <- ks, let v = fromMaybe 0 $ snd <$> Map.lookupLE k m]
  avgMaps = Map.map (/ fromIntegral numNodes) . Map.unionsWith (+) . sampleCdfs

weightedSamplesToPmf :: (Ord v, Fractional r) => r -> [(v, r)] -> Map v r
weightedSamplesToPmf total = Map.map (/ total) . Map.fromListWith (+)

unitSamplesToPmf :: (Ord v, Fractional r) => r -> [v] -> Map v r
unitSamplesToPmf total vs = weightedSamplesToPmf total [(v, 1) | v <- vs]

pmfToCdf :: (Ord v, Num r) => Map v r -> Map v r
pmfToCdf pmf0 = Map.fromAscList $ zip (Map.keys pmf0) (scanl1 (+) $ Map.elems pmf0)

entriesToLatencyCdfs ::
  Map NodeId StakeFraction ->
  [DiffusionEntry id] ->
  Set.Set StakeFraction ->
  Map StakeFraction (Map DiffTime Micro)
entriesToLatencyCdfs stakes entries stakeBins =
  Map.map (pmfToCdf . unitSamplesToPmf numBlocks)
    . flip transposeLatenciesPerStake stakeBins
    $ [ diffusionLatencyPerStakeFraction stakes slot_start adoptions
      | DiffusionEntry{..} <- entries
      , let slot_start = fromIntegral (floor created :: Integer) -- assumes generation takes less than one second
      ]
 where
  numBlocks = fromIntegral (length entries)

---------------------------------------------------
---- Convenience functions

-- Using ToJSON because DiffTime add `s` for show.
-- Added `Num` constraint to catch avoid more complex types.
cdfToCsvFile :: (Num r, Num v, ToJSON r, ToJSON v) => FilePath -> Map v r -> IO ()
cdfToCsvFile fp m =
  BSL8.writeFile fp $
    BSL8.unlines $
      [ encode v <> BSL8.pack ", " <> encode r
      | (v, r) <- Map.toList m
      ]

ibDiffusionCdfs
  , ebDiffusionCdfs
  , vtDiffusionCdfs
  , rbDiffusionCdfs ::
    RawLeiosData -> Set.Set StakeFraction -> Map StakeFraction (Map DiffTime Micro)
ibDiffusionCdfs raw stakes = entriesToLatencyCdfs raw.p2p_network.p2pNodeStakes raw.ib_diffusion_entries stakes
ebDiffusionCdfs raw stakes = entriesToLatencyCdfs raw.p2p_network.p2pNodeStakes raw.eb_diffusion_entries stakes
vtDiffusionCdfs raw stakes = entriesToLatencyCdfs raw.p2p_network.p2pNodeStakes raw.vt_diffusion_entries stakes
rbDiffusionCdfs raw stakes = entriesToLatencyCdfs raw.p2p_network.p2pNodeStakes raw.rb_diffusion_entries stakes

data BlockDiffusionConfig = BlockDiffusionConfig
  { generationDelay :: !DiffTime
  , validationDelay :: !DiffTime
  -- ^ both header and body, if it applies
  , hops :: !Int
  , size :: !Bytes
  }
  deriving (Show)

idealDiffusionTimes :: P2PNetwork -> BlockDiffusionConfig -> P2PIdealDiffusionTimes
idealDiffusionTimes p2pNetwork@P2PNetwork{p2pLinks} BlockDiffusionConfig{..} =
  p2pGraphIdealDiffusionTimes (networkToTopology p2pNetwork) generationDelay validationDelay (\n1 n2 _ -> communicationDelay n1 n2)
 where
  communicationDelay n1 n2 = latency * fromIntegral hops + serialization + deserialization
   where
    (secondsToDiffTime -> latency, bandwidth) = fromMaybe undefined (Map.lookup (n1, n2) p2pLinks)
    serialization = case bandwidth of
      Nothing -> 0
      Just bps -> secondsToDiffTime $ realToFrac size / realToFrac bps
    deserialization = serialization

idealEntry :: P2PIdealDiffusionTimes -> DiffusionEntry id -> DiffusionEntry id
idealEntry idealTimes DiffusionEntry{..} =
  DiffusionEntry
    { adoptions = reverse $ p2pGraphIdealDiffusionTimesFromNode' idealTimes (NodeId node_id) -- TODO: remove some reverse
    , created = 0
    , ..
    }

idealEntries :: P2PNetwork -> BlockDiffusionConfig -> [DiffusionEntry id] -> [DiffusionEntry id]
idealEntries p2pNetwork bdCfg es = map (idealEntry idealTimes) es
 where
  idealTimes = idealDiffusionTimes p2pNetwork bdCfg

data SomeDiffusionEntries = forall id. (ToJSON id, Ord id) => SomeDE [DiffusionEntry id]

reportLeiosData :: FilePath -> FilePath -> [Micro] -> IO ()
reportLeiosData prefixDir simDataFile stakes = do
  Just simDataVal <- decodeFileStrict @Value simDataFile
  let
    !raw = either error id $ parseEither (withObject "Object" $ \o -> parseJSON @RawLeiosData =<< (o .: "raw")) simDataVal
    !stakesSet = Set.fromList $ map (StakeFraction . realToFrac) stakes
  let
    leios = convertConfig raw.config
    relayHops = 3
    praosHops = 3
    fullIB = mockFullInputBlock leios
    fullEB = mockFullEndorseBlock leios
    fullVT = mockFullVoteMsg leios
    fullRB = mockFullRankingBlock leios
    ibCfg =
      BlockDiffusionConfig
        { generationDelay = leios.delays.inputBlockGeneration fullIB
        , validationDelay =
            leios.delays.inputBlockHeaderValidation fullIB.header
              + leios.delays.inputBlockValidation fullIB
        , size = messageSizeBytes fullIB
        , hops = relayHops
        }
    ebCfg =
      BlockDiffusionConfig
        { generationDelay = leios.delays.endorseBlockGeneration fullEB
        , validationDelay = leios.delays.endorseBlockValidation fullEB
        , size = messageSizeBytes fullEB
        , hops = relayHops
        }
    vtCfg =
      BlockDiffusionConfig
        { generationDelay =
            leios.delays.voteMsgGeneration
              fullVT
              [ EndorseBlock{id = id', ..}
              | id' <- fullVT.endorseBlocks
              , let EndorseBlock
                      { slot
                      , producer
                      , inputBlocks
                      , endorseBlocksEarlierStage
                      , endorseBlocksEarlierPipeline
                      , size
                      } = fullEB
              ]
        , validationDelay = leios.delays.voteMsgValidation fullVT
        , size = messageSizeBytes fullVT
        , hops = praosHops
        }
    rbCfg =
      BlockDiffusionConfig
        { generationDelay = leios.praos.blockGenerationDelay fullRB
        , validationDelay =
            leios.praos.headerValidationDelay fullRB.blockHeader
              + leios.praos.blockValidationDelay fullRB
        , size = messageSizeBytes fullRB
        , hops = relayHops
        }
    rawEntries =
      [ ("IB", ibCfg, SomeDE raw.ib_diffusion_entries)
      , ("EB", ebCfg, SomeDE raw.eb_diffusion_entries)
      , ("VT", vtCfg, SomeDE raw.vt_diffusion_entries)
      , ("RB", rbCfg, SomeDE raw.rb_diffusion_entries)
      ]
  forM_ rawEntries $ reportDE prefixDir raw.p2p_network stakesSet

normalizeEntry :: DiffusionEntry id -> DiffusionEntry id
normalizeEntry DiffusionEntry{..} =
  DiffusionEntry{created = 0, adoptions = reverse $ sortOn snd $ Map.toList $ Map.map (\x -> x - slot_start) $ Map.fromListWith min adoptions, ..}
 where
  slot_start = realToFrac (floor created :: Integer)

reportDE :: FilePath -> P2PNetwork -> Set.Set StakeFraction -> (String, BlockDiffusionConfig, SomeDiffusionEntries) -> IO ()
reportDE prefixDir p2p_network stakes (tag, bdCfg, SomeDE (map normalizeEntry -> simEntries)) = do
  let mkCdfs es = entriesToLatencyCdfs p2p_network.p2pNodeStakes es stakes
  let csvPath mid end (StakeFraction f) = prefixDir </> mid <> "-" <> show f <> end <.> "csv"
      writeCsvFiles mkfn m = assert (Map.keysSet m == stakes) $ forM_ (Map.toList m) $ \(s, cdf) ->
        cdfToCsvFile (mkfn s) cdf
  writeCsvFiles (csvPath tag "") (mkCdfs simEntries)
  writeCsvFiles (csvPath tag "-ideal") (mkCdfs (idealEntries p2p_network bdCfg simEntries))
