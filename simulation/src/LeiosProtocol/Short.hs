{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Short (module LeiosProtocol.Short, DiffusionStrategy (..)) where

import Chan (mkConnectionConfig)
import Control.Exception (assert)
import Control.Monad (guard)
import Data.Kind
import Data.List
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (
  fromMaybe,
  mapMaybe,
  maybeToList,
 )
import Data.Ord
import Data.Word (Word16)
import LeiosProtocol.Common
import LeiosProtocol.Config as OnDisk
import ModelTCP
import Prelude hiding (id)

-- | The sizes here are prescriptive, used to fill in fields that MessageSize will read from.
data SizesConfig = SizesConfig
  { inputBlockHeader :: !Bytes
  , inputBlockBodyAvgSize :: !Bytes
  -- ^ as we do not model transactions we just use a fixed size for bodies.
  , inputBlockBodyMaxSize :: !Bytes
  , endorseBlock :: !(EndorseBlock -> Bytes)
  , voteMsg :: !(VoteMsg -> Bytes)
  , certificate :: !(Certificate -> Bytes)
  -- ^ certificate size depends on number of votes, contributes to RB block body sizes.
  , rankingBlockLegacyPraosPayloadAvgSize :: !Bytes
  -- ^ txs possibly included.
  }

-- Note: ranking block validation delays are in the PraosConfig, covers certificate validation.
data LeiosDelays = LeiosDelays
  { inputBlockGeneration :: !(InputBlock -> DiffTime)
  , inputBlockHeaderValidation :: !(InputBlockHeader -> DiffTime)
  -- ^ vrf and signature
  , inputBlockValidation :: !(InputBlock -> DiffTime)
  -- ^ hash matching and payload validation (incl. tx scripts)
  , endorseBlockGeneration :: !(EndorseBlock -> DiffTime)
  , endorseBlockValidation :: !(EndorseBlock -> DiffTime)
  , voteMsgGeneration :: !(VoteMsg -> [EndorseBlock] -> DiffTime)
  , voteMsgValidation :: !(VoteMsg -> DiffTime)
  , certificateGeneration :: !(Certificate -> DiffTime)
  , certificateValidation :: !(Certificate -> DiffTime)
  }

prioritize ::
  DiffusionStrategy ->
  (header -> SlotNo) ->
  -- | available to request
  Map id header ->
  -- | same headers in the order we received them from peer.
  [header] ->
  [header]
prioritize PeerOrder _ = \_ hs -> hs
prioritize FreshestFirst sl = \m _ -> sortOn (Down . sl) . Map.elems $ m
prioritize OldestFirst sl = \m _ -> sortOn sl . Map.elems $ m

data SingPipeline (p :: Pipeline) where
  SingSingleVote :: SingPipeline SingleVote
  SingSplitVote :: SingPipeline SplitVote

data RelayDiffusionConfig = RelayDiffusionConfig
  { strategy :: !DiffusionStrategy
  , maxWindowSize :: !Word16
  , maxHeadersToRequest :: !Word16
  , maxBodiesToRequest :: !Word16
  }

data LeiosConfig = forall p. IsPipeline p => LeiosConfig
  { praos :: PraosConfig RankingBlockBody
  , pipeline :: SingPipeline p
  , sliceLength :: Int
  -- ^ measured in slots, also stage length in Short leios.
  , inputBlockFrequencyPerSlot :: Double
  -- ^ expected InputBlock generation rate per slot.
  , endorseBlockFrequencyPerStage :: Double
  -- ^ expected EndorseBlock generation rate per stage, at most one per _node_ in each (pipeline, stage).
  , activeVotingStageLength :: Int
  -- ^ prefix of the voting stage where new votes are generated, <= sliceLength.
  , votingFrequencyPerStage :: Double
  , voteSendStage :: Stage p
  , votesForCertificate :: Int
  , sizes :: SizesConfig
  , delays :: LeiosDelays
  , ibDiffusion :: RelayDiffusionConfig
  , ebDiffusion :: RelayDiffusionConfig
  , voteDiffusion :: RelayDiffusionConfig
  , relayStrategy :: RelayStrategy
  }

data SomeStage = forall p. IsPipeline p => SomeStage (SingPipeline p) (Stage p)

convertConfig :: OnDisk.Config -> LeiosConfig
convertConfig disk =
  case voting of
    SomeStage pipeline voteSendStage ->
      LeiosConfig
        { praos
        , pipeline
        , voteSendStage
        , sliceLength = fromIntegral disk.leiosStageLengthSlots
        , inputBlockFrequencyPerSlot = disk.ibGenerationProbability
        , endorseBlockFrequencyPerStage = disk.ebGenerationProbability
        , activeVotingStageLength = fromIntegral disk.leiosStageActiveVotingSlots
        , votingFrequencyPerStage = disk.voteGenerationProbability
        , votesForCertificate = fromIntegral disk.voteThreshold
        , sizes
        , delays
        , ibDiffusion =
            RelayDiffusionConfig
              { strategy = disk.ibDiffusionStrategy
              , maxWindowSize = disk.ibDiffusionMaxWindowSize
              , maxHeadersToRequest = disk.ibDiffusionMaxHeadersToRequest
              , maxBodiesToRequest = disk.ibDiffusionMaxBodiesToRequest
              }
        , ebDiffusion =
            RelayDiffusionConfig
              { strategy = disk.ebDiffusionStrategy
              , maxWindowSize = disk.ebDiffusionMaxWindowSize
              , maxHeadersToRequest = disk.ebDiffusionMaxHeadersToRequest
              , maxBodiesToRequest = disk.ebDiffusionMaxBodiesToRequest
              }
        , voteDiffusion =
            RelayDiffusionConfig
              { strategy = disk.voteDiffusionStrategy
              , maxWindowSize = disk.voteDiffusionMaxWindowSize
              , maxHeadersToRequest = disk.voteDiffusionMaxHeadersToRequest
              , maxBodiesToRequest = disk.voteDiffusionMaxBodiesToRequest
              }
        , relayStrategy = disk.relayStrategy
        }
 where
  forEach n xs = n * fromIntegral (length xs)
  forEachKey n m = n * fromIntegral (Map.size m)
  durationMsToDiffTime (DurationMs d) = secondsToDiffTime $ d / 1000
  voting =
    if disk.leiosVoteSendRecvStages
      then SomeStage SingSplitVote VoteSend
      else SomeStage SingSingleVote Vote
  praos =
    PraosConfig
      { blockFrequencyPerSlot = disk.rbGenerationProbability
      , headerSize = fromIntegral disk.ibHeadSizeBytes
      , bodySize = \body ->
          1
            + sum (map (certificateSize . snd) body.endorseBlocks)
            + body.payload
      , bodyMaxSize = fromIntegral disk.rbBodyMaxSizeBytes
      , blockValidationDelay = \(Block _ body) ->
          let legacy
                | body.payload > 0 =
                    durationMsToDiffTime $
                      disk.rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant
                        + disk.rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte * fromIntegral body.payload
                | otherwise = 0
           in legacy
                + sum (map (certificateValidation . snd) body.endorseBlocks)
      , headerValidationDelay = const $ durationMsToDiffTime disk.ibHeadValidationCpuTimeMs
      , blockGenerationDelay = \(Block _ body) ->
          durationMsToDiffTime disk.rbGenerationCpuTimeMs
            + sum (map (certificateGeneration . snd) body.endorseBlocks)
      , configureConnection = mkConnectionConfig (tcpCongestionControl disk) (multiplexMiniProtocols disk)
      , relayStrategy = disk.relayStrategy
      }
  certificateSize (Certificate votesMap) =
    fromIntegral $
      disk.certSizeBytesConstant
        + disk.certSizeBytesPerNode `forEachKey` votesMap
  sizes =
    SizesConfig
      { inputBlockHeader = fromIntegral disk.ibHeadSizeBytes
      , inputBlockBodyAvgSize = fromIntegral disk.ibBodyAvgSizeBytes
      , inputBlockBodyMaxSize = fromIntegral disk.ibBodyMaxSizeBytes
      , endorseBlock = \eb ->
          fromIntegral $
            disk.ebSizeBytesConstant
              + disk.ebSizeBytesPerIb `forEach` eb.inputBlocks
      , voteMsg = \vt ->
          fromIntegral $
            disk.voteBundleSizeBytesConstant
              + disk.voteBundleSizeBytesPerEb `forEach` vt.endorseBlocks
      , certificate = const $ error "certificate size config already included in PraosConfig{bodySize}"
      , rankingBlockLegacyPraosPayloadAvgSize = fromIntegral disk.rbBodyLegacyPraosPayloadAvgSizeBytes
      }
  certificateGeneration (Certificate votesMap) =
    durationMsToDiffTime $
      disk.certGenerationCpuTimeMsConstant
        + disk.certGenerationCpuTimeMsPerNode `forEachKey` votesMap
  certificateValidation (Certificate votesMap) =
    durationMsToDiffTime $
      disk.certValidationCpuTimeMsConstant
        + disk.certValidationCpuTimeMsPerNode `forEachKey` votesMap
  delays =
    LeiosDelays
      { inputBlockGeneration = const $ durationMsToDiffTime disk.ibGenerationCpuTimeMs
      , inputBlockHeaderValidation = const $ durationMsToDiffTime disk.ibHeadValidationCpuTimeMs
      , inputBlockValidation = \ib ->
          durationMsToDiffTime $
            disk.ibBodyValidationCpuTimeMsConstant
              + disk.ibBodyValidationCpuTimeMsPerByte * fromIntegral ib.body.size
      , endorseBlockGeneration = const $ durationMsToDiffTime disk.ebGenerationCpuTimeMs
      , endorseBlockValidation = const $ durationMsToDiffTime disk.ebValidationCpuTimeMs
      , -- TODO: can parallelize?
        voteMsgGeneration = \vm ebs ->
          assert (vm.endorseBlocks == map (.id) ebs) $
            durationMsToDiffTime $
              sum
                [ disk.voteGenerationCpuTimeMsConstant
                  + disk.voteGenerationCpuTimeMsPerIb `forEach` eb.inputBlocks
                | eb <- ebs
                ]
      , voteMsgValidation = \vm ->
          durationMsToDiffTime $
            disk.voteValidationCpuTimeMs `forEach` vm.endorseBlocks
      , certificateGeneration = const $ error "certificateGeneration delay included in RB generation"
      , certificateValidation = const $ error "certificateValidation delay included in RB validation"
      }

class FixSize a where
  fixSize :: LeiosConfig -> a -> a

instance FixSize InputBlockHeader where
  fixSize cfg InputBlockHeader{..} =
    InputBlockHeader
      { size = cfg.sizes.inputBlockHeader
      , ..
      }

instance FixSize EndorseBlock where
  fixSize cfg eb@EndorseBlock{..} =
    EndorseBlock
      { size = cfg.sizes.endorseBlock eb
      , ..
      }

instance FixSize VoteMsg where
  fixSize cfg v@VoteMsg{..} =
    VoteMsg
      { size = cfg.sizes.voteMsg v
      , ..
      }

instance FixSize RankingBlockHeader where
  fixSize cfg rh = rh{headerMessageSize = cfg.praos.headerSize}
instance FixSize RankingBlockBody where
  fixSize cfg rb@RankingBlockBody{..} =
    RankingBlockBody
      { size = cfg.praos.bodySize rb
      , ..
      }
instance FixSize body => FixSize (Block body) where
  fixSize cfg (Block h b) = Block (fixSize cfg h) (fixSize cfg b)

-----------------------------------------------------------
---- Stages
-----------------------------------------------------------

data Pipeline = SingleVote | SplitVote

data Stage :: Pipeline -> Type where
  Propose, Deliver1, Deliver2, Endorse :: Stage a
  Vote :: Stage SingleVote
  VoteSend, VoteRecv :: Stage SplitVote

deriving instance Eq (Stage a)
deriving instance Ord (Stage a)
deriving instance Show (Stage a)

-- TODO: find better representation
class IsPipeline (a :: Pipeline) where
  allStages :: [Stage a]
instance IsPipeline SingleVote where
  allStages = [Propose, Deliver1, Deliver2, Endorse, Vote]
instance IsPipeline SplitVote where
  allStages = [Propose, Deliver1, Deliver2, Endorse, VoteSend, VoteRecv]
instance IsPipeline a => Enum (Stage a) where
  toEnum n = allStages !! n
  fromEnum s = fromMaybe undefined $ findIndex (s ==) allStages
instance IsPipeline a => Bounded (Stage a) where
  minBound = case allStages of
    (x : _) -> x
    [] -> undefined
  maxBound = last allStages

inRange :: SlotNo -> (SlotNo, SlotNo) -> Bool
inRange s (a, b) = a <= s && s <= b

rangePrefix :: Int -> (SlotNo, SlotNo) -> (SlotNo, SlotNo)
rangePrefix l (start, _) = (start, toEnum $ fromEnum start + l - 1)

-- | Returns inclusive range of slots.
stageRange ::
  IsPipeline p =>
  LeiosConfig ->
  -- | current stage of pipeline
  Stage p ->
  -- | current slot
  SlotNo ->
  -- | stage to compute the range for
  Stage p ->
  Maybe (SlotNo, SlotNo)
stageRange cfg = stageRange' cfg.sliceLength

stageRange' :: IsPipeline p => Int -> Stage p -> SlotNo -> Stage p -> Maybe (SlotNo, SlotNo)
stageRange' l s0 slot s = slice l slot (fromEnum s0 - fromEnum s)

prop_stageRange' :: forall p. IsPipeline p => Int -> SlotNo -> Bool
prop_stageRange' l slot =
  and [Just True == ((slot `inRange`) <$> stageRange' @p l stage slot stage) | stage <- stages]
    && and [contiguous $ mapMaybe (stageRange' l stage slot) stages | stage <- stages]
 where
  stages = [minBound .. maxBound]
  rightSize (a, b) = length [a .. b] == l
  contiguous (x : y : xs) = rightSize x && succ (snd x) == fst y && contiguous (y : xs)
  contiguous _ = True

stageEnd :: IsPipeline p => LeiosConfig -> Stage p -> SlotNo -> Stage p -> Maybe SlotNo
stageEnd l s0 slot s = snd <$> stageRange l s0 slot s

stageStart :: IsPipeline p => LeiosConfig -> Stage p -> SlotNo -> Stage p -> Maybe SlotNo
stageStart l s0 slot s = fst <$> stageRange l s0 slot s

-- | Assumes pipelines start at slot 0 and keep going.
isStage :: IsPipeline p => LeiosConfig -> Stage p -> SlotNo -> Bool
isStage cfg stage slot = fromEnum slot >= cfg.sliceLength * fromEnum stage

newtype PipelineNo = PipelineNo Word64
  deriving (Bounded, Enum, Show, Eq, Ord)

stageRangeOf :: forall p. IsPipeline p => LeiosConfig -> PipelineNo -> Stage p -> (SlotNo, SlotNo)
stageRangeOf cfg pl stage =
  fromMaybe
    undefined
    (stageRange cfg minBound (toEnum (fromEnum pl * cfg.sliceLength)) stage)

pipelineOf :: forall p. IsPipeline p => LeiosConfig -> Stage p -> SlotNo -> PipelineNo
pipelineOf cfg stage sl =
  toEnum $
    fromMaybe undefined (fromEnum <$> stageStart cfg stage sl minBound)
      `div` cfg.sliceLength

----------------------------------------------------------------------------------------------
---- Smart constructors
----------------------------------------------------------------------------------------------

mkRankingBlockBody :: LeiosConfig -> NodeId -> Maybe (EndorseBlockId, Certificate) -> Bytes -> RankingBlockBody
mkRankingBlockBody cfg nodeId ebs payload = rb
 where
  rb =
    fixSize cfg $
      RankingBlockBody
        { endorseBlocks = maybeToList ebs
        , payload
        , nodeId
        , size = 0
        }

mkInputBlockHeader ::
  LeiosConfig ->
  InputBlockId ->
  SlotNo ->
  SubSlotNo ->
  NodeId ->
  ChainHash RankingBlock ->
  InputBlockHeader
mkInputBlockHeader cfg id slot subSlot producer rankingBlock =
  fixSize cfg $ InputBlockHeader{size = 0, ..}

mkInputBlock :: LeiosConfig -> InputBlockHeader -> Bytes -> InputBlock
mkInputBlock _cfg header bodySize = assert (messageSizeBytes ib >= segmentSize) ib
 where
  ib = InputBlock{header, body = InputBlockBody{id = header.id, size = bodySize, slot = header.slot}}

forEachPipeline :: (forall p. Stage p) -> (forall p. IsPipeline p => Stage p -> a) -> [a]
forEachPipeline s k = [k @SingleVote s, k @SplitVote s]

mkEndorseBlock ::
  LeiosConfig -> EndorseBlockId -> SlotNo -> NodeId -> [InputBlockId] -> EndorseBlock
mkEndorseBlock cfg@LeiosConfig{pipeline = _ :: SingPipeline p} id slot producer inputBlocks =
  -- Endorse blocks are produced at the beginning of the stage.
  assert (stageStart @p cfg Endorse slot Endorse == Just slot) $
    fixSize cfg $
      EndorseBlock{endorseBlocksEarlierStage = [], endorseBlocksEarlierPipeline = [], size = 0, ..}

mkVoteMsg :: LeiosConfig -> VoteId -> SlotNo -> NodeId -> Word64 -> [EndorseBlockId] -> VoteMsg
mkVoteMsg cfg id slot producer votes endorseBlocks = fixSize cfg $ VoteMsg{size = 0, ..}

mkCertificate :: LeiosConfig -> Map VoteId Word64 -> Certificate
mkCertificate cfg vs =
  assert (fromIntegral cfg.votesForCertificate <= sum (Map.elems vs)) $
    Certificate vs

---------------------------------------------------------------------------------------
---- Selecting data to build blocks
---------------------------------------------------------------------------------------

-- Buffers views, divided to avoid reading unneeded buffers.

data NewRankingBlockData = NewRankingBlockData
  { freshestCertifiedEB :: Maybe (EndorseBlockId, Certificate)
  , txsPayload :: Bytes
  }

data NewInputBlockData = NewInputBlockData
  { referenceRankingBlock :: ChainHash RankingBlock
  -- ^ points to prefix of current chain with ledger state computed.
  , txsPayload :: Bytes
  }

newtype InputBlocksSnapshot = InputBlocksSnapshot
  { validInputBlocks :: InputBlocksQuery -> [InputBlockId]
  }

newtype EndorseBlocksSnapshot = EndorseBlocksSnapshot
  { validEndorseBlocks :: (SlotNo, SlotNo) -> [EndorseBlock]
  }

-- | Both constraints are inclusive.
data InputBlocksQuery = InputBlocksQuery
  { generatedBetween :: (SlotNo, SlotNo)
  , receivedBy :: SlotNo
  -- ^ This is checked against time the body is downloaded, before validation.
  }

inputBlocksToEndorse ::
  LeiosConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  [InputBlockId]
inputBlocksToEndorse cfg@LeiosConfig{pipeline = _ :: SingPipeline p} current buffer = fromMaybe [] $ do
  generatedBetween <- stageRange @p cfg Endorse current Propose
  receivedBy <- stageEnd @p cfg Endorse current Deliver2
  pure $
    buffer.validInputBlocks
      InputBlocksQuery
        { generatedBetween
        , receivedBy
        }

shouldVoteOnEB ::
  LeiosConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  EndorseBlock ->
  Bool
shouldVoteOnEB cfg@LeiosConfig{voteSendStage} slot _buffers
  | Nothing <- stageRange cfg voteSendStage slot Propose = const False
shouldVoteOnEB cfg@LeiosConfig{voteSendStage} slot buffers = cond
 where
  generatedBetween = fromMaybe (error "impossible") $ stageRange cfg voteSendStage slot Propose
  receivedByEndorse =
    buffers.validInputBlocks
      InputBlocksQuery
        { generatedBetween
        , receivedBy = fromMaybe (error "impossible") $ stageEnd cfg voteSendStage slot Endorse
        }
  receivedByDeliver1 = buffers.validInputBlocks q
   where
    q =
      InputBlocksQuery
        { generatedBetween
        , receivedBy = fromMaybe (error "impossible") $ stageEnd cfg voteSendStage slot Deliver1
        }
  -- Order of references in EndorseBlock matters for ledger state, so we stick to lists.
  -- Note: maybe order on (slot, subSlot, vrf proof) should be used instead?
  subset xs ys = all (`elem` ys) xs

  cond :: EndorseBlock -> Bool
  cond eb = assert assumptions $ acd && b
   where
    assumptions =
      null eb.endorseBlocksEarlierStage
        && null eb.endorseBlocksEarlierPipeline
        && eb.slot `inRange` fromMaybe (error "impossible") (stageRange cfg voteSendStage slot Endorse)
    -- A. all referenced IBs have been received by the end of the Endorse stage,
    -- C. all referenced IBs validate (wrt. script execution), and,
    -- D. only IBs from this pipeline’s Propose stage are referenced (and not from other pipelines).
    acd = eb.inputBlocks `subset` receivedByEndorse
    -- B. all IBs seen by the end of the Deliver 1 stage are referenced,
    b = receivedByDeliver1 `subset` eb.inputBlocks

endorseBlocksToVoteFor ::
  LeiosConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  EndorseBlocksSnapshot ->
  [EndorseBlock]
endorseBlocksToVoteFor cfg@LeiosConfig{voteSendStage} slot ibs ebs =
  let cond = shouldVoteOnEB cfg slot ibs
   in filter cond $
        maybe [] ebs.validEndorseBlocks (stageRange cfg voteSendStage slot Endorse)

endorseBlockPipeline :: LeiosConfig -> EndorseBlock -> PipelineNo
endorseBlockPipeline cfg@LeiosConfig{pipeline = _ :: SingPipeline p} eb = pipelineOf @p cfg Endorse eb.slot

-----------------------------------------------------------------
---- Expected generation rates in each slot.
-----------------------------------------------------------------

splitIntoSubSlots :: NetworkRate -> [NetworkRate]
splitIntoSubSlots (NetworkRate r)
  | r <= 1 = [NetworkRate r]
  | otherwise =
      let
        q = ceiling r
        fq = NetworkRate $ r / fromIntegral q
       in
        replicate q fq

inputBlockRate :: LeiosConfig -> StakeFraction -> SlotNo -> Maybe (Double -> Word64)
inputBlockRate cfg@LeiosConfig{inputBlockFrequencyPerSlot, pipeline = _ :: SingPipeline p} stake
  | inputBlockFrequencyPerSlot > 1 =
      case sortition stake networkRate of
        Sortition f -> checkSlot f
  | otherwise =
      case nodeRate stake networkRate of
        NodeRate r -> checkSlot (\p -> if p <= r then 1 else 0)
 where
  networkRate = NetworkRate inputBlockFrequencyPerSlot
  checkSlot g slot = assert (isStage @p cfg Propose slot) $ Just g

endorseBlockRate :: LeiosConfig -> StakeFraction -> SlotNo -> Maybe (Double -> Word64)
endorseBlockRate cfg@LeiosConfig{pipeline = _ :: SingPipeline p} stake
  | cfg.endorseBlockFrequencyPerStage > 1 =
      case sortition stake networkRate of
        Sortition f -> checkSlot f
  | otherwise =
      case nodeRate stake networkRate of
        NodeRate r -> checkSlot (\p -> if p <= r then 1 else 0)
 where
  networkRate = NetworkRate cfg.endorseBlockFrequencyPerStage
  checkSlot f = \slot -> do
    guard $ isStage @p cfg Endorse slot
    startEndorse <- stageStart @p cfg Endorse slot Endorse
    guard $ startEndorse == slot
    return $ min 1 . f

votingRanges :: LeiosConfig -> [(SlotNo, SlotNo)]
votingRanges cfg@LeiosConfig{voteSendStage} = go 0
 where
  go slot =
    case rangePrefix cfg.activeVotingStageLength <$> stageRange cfg minBound slot voteSendStage of
      Just r -> r : go nextSlot
      Nothing -> go nextSlot
   where
    nextSlot = toEnum $ fromEnum slot + cfg.sliceLength

votingRatePerPipeline :: LeiosConfig -> StakeFraction -> Double -> Word64
votingRatePerPipeline cfg stake = f
 where
  !(Sortition f) = sortition stake $ NetworkRate cfg.votingFrequencyPerStage

nodeRate :: StakeFraction -> NetworkRate -> NodeRate
nodeRate (StakeFraction s) (NetworkRate r) = NodeRate (s * r)

-- | Returns a cache of thresholds for being awarded some number of wins.
--   Keys are calculated to match the accumulator values from `voter_check` in `crypto-benchmarks.rs`.
--
--   Note: We compute the keys using `Rational` for extra precision, then convert to Double to avoid memory issues.
--         We should be doing this with a quadruple precision floating point type to match the Rust code, but support for that is lacking.
sortitionTable ::
  StakeFraction ->
  NetworkRate ->
  Map Double Word64
sortitionTable (StakeFraction s) (NetworkRate votes) = Map.fromAscList $ zip (map realToFrac $ scanl (+) 0 foos) [0 .. floor votes]
 where
  foos = 1 : zipWith (\ii prev -> prev * x / ii) [1 ..] foos
  x = realToFrac s * realToFrac votes :: Rational

numWins ::
  Num a =>
  StakeFraction ->
  NetworkRate ->
  Map Double a ->
  -- | VRF value
  Double ->
  a
numWins (StakeFraction sigma) (NetworkRate rate) m p =
  maybe 0 snd $ Map.lookupLT (realToFrac p / realToFrac (exp $ negate (rate * sigma))) m

-- | Datatype used to mark a sortition closure that should be kept and reused across slots.
--   `data` rather than `newtype` so setup computations can be triggered by matching.
data Sortition = Sortition (Double -> Word64)

sortition :: StakeFraction -> NetworkRate -> Sortition
sortition stake rate =
  let
    !table = sortitionTable stake rate
   in
    Sortition (numWins stake rate table)
