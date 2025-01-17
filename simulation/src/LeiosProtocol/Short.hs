{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Short where

import Control.Exception (assert)
import Control.Monad (guard)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (
  fromMaybe,
  isNothing,
  mapMaybe,
  maybeToList,
 )
import LeiosProtocol.Common
import LeiosProtocol.Config as OnDisk
import ModelTCP
import PraosProtocol.Common (Block (..))
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
  , voteMsgGeneration :: !(VoteMsg -> DiffTime)
  , voteMsgValidation :: !(VoteMsg -> DiffTime)
  , certificateGeneration :: !(Certificate -> DiffTime)
  , certificateValidation :: !(Certificate -> DiffTime)
  }

-- TODO: add feature flags to generalize from (Uniform) Short leios to other variants.
--       Would need to rework def. of Stage to accomodate different pipeline shapes.
data LeiosConfig = LeiosConfig
  { praos :: PraosConfig RankingBlockBody
  , sliceLength :: Int
  -- ^ measured in slots, also stage length in Short leios.
  , inputBlockFrequencyPerSlot :: Double
  -- ^ expected InputBlock generation rate per slot.
  , endorseBlockFrequencyPerStage :: Double
  -- ^ expected EndorseBlock generation rate per stage, at most one per _node_ in each (pipeline, stage).
  , activeVotingStageLength :: Int
  -- ^ prefix of the voting stage where new votes are generated, <= sliceLength.
  , votingFrequencyPerStage :: Double
  , votesForCertificate :: Int
  , sizes :: SizesConfig
  , delays :: LeiosDelays
  }

convertConfig :: OnDisk.Config -> LeiosConfig
convertConfig = error "TBD"

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

data Stage = Propose | Deliver1 | Deliver2 | Endorse | Vote
  deriving (Eq, Ord, Show, Enum, Bounded)

inRange :: SlotNo -> (SlotNo, SlotNo) -> Bool
inRange s (a, b) = a <= s && s <= b

rangePrefix :: Int -> (SlotNo, SlotNo) -> (SlotNo, SlotNo)
rangePrefix l (start, _) = (start, toEnum $ fromEnum start + l - 1)

-- | Returns inclusive range of slots.
stageRange ::
  LeiosConfig ->
  -- | current stage of pipeline
  Stage ->
  -- | current slot
  SlotNo ->
  -- | stage to compute the range for
  Stage ->
  Maybe (SlotNo, SlotNo)
stageRange cfg = stageRange' cfg.sliceLength

stageRange' :: Int -> Stage -> SlotNo -> Stage -> Maybe (SlotNo, SlotNo)
stageRange' l s0 slot s = slice l slot (fromEnum s0 - fromEnum s)

prop_stageRange' :: Int -> SlotNo -> Bool
prop_stageRange' l slot =
  and [Just True == ((slot `inRange`) <$> stageRange' l stage slot stage) | stage <- stages]
    && and [contiguous $ mapMaybe (stageRange' l stage slot) stages | stage <- stages]
 where
  stages = [minBound .. maxBound]
  rightSize (a, b) = length [a .. b] == l
  contiguous (x : y : xs) = rightSize x && succ (snd x) == fst y && contiguous (y : xs)
  contiguous _ = True

stageEnd :: LeiosConfig -> Stage -> SlotNo -> Stage -> Maybe SlotNo
stageEnd l s0 slot s = snd <$> stageRange l s0 slot s

stageStart :: LeiosConfig -> Stage -> SlotNo -> Stage -> Maybe SlotNo
stageStart l s0 slot s = fst <$> stageRange l s0 slot s

-- | Assumes pipelines start at slot 0 and keep going.
isStage :: LeiosConfig -> Stage -> SlotNo -> Bool
isStage cfg stage slot = fromEnum slot >= cfg.sliceLength * fromEnum stage

----------------------------------------------------------------------------------------------
---- Smart constructors
----------------------------------------------------------------------------------------------

mkRankingBlockBody :: LeiosConfig -> NodeId -> Maybe (EndorseBlockId, Certificate) -> Bytes -> RankingBlockBody
mkRankingBlockBody cfg nodeId ebs payload = assert (isNothing ebs || messageSizeBytes rb >= segmentSize) rb
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

mkEndorseBlock ::
  LeiosConfig -> EndorseBlockId -> SlotNo -> NodeId -> [InputBlockId] -> EndorseBlock
mkEndorseBlock cfg id slot producer inputBlocks =
  -- Endorse blocks are produced at the beginning of the stage.
  assert (stageStart cfg Endorse slot Endorse == Just slot) $
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
inputBlocksToEndorse cfg current buffer = fromMaybe [] $ do
  generatedBetween <- stageRange cfg Endorse current Propose
  receivedBy <- stageEnd cfg Endorse current Deliver2
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
shouldVoteOnEB cfg slot _buffers | Nothing <- stageRange cfg Vote slot Propose = const False
shouldVoteOnEB cfg slot buffers = cond
 where
  generatedBetween = fromMaybe (error "impossible") $ stageRange cfg Vote slot Propose
  receivedByEndorse =
    buffers.validInputBlocks
      InputBlocksQuery
        { generatedBetween
        , receivedBy = fromMaybe (error "impossible") $ stageEnd cfg Vote slot Endorse
        }
  receivedByDeliver1 = buffers.validInputBlocks q
   where
    q =
      InputBlocksQuery
        { generatedBetween
        , receivedBy = fromMaybe (error "impossible") $ stageEnd cfg Vote slot Deliver1
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
        && eb.slot `inRange` fromMaybe (error "impossible") (stageRange cfg Vote slot Endorse)
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
  [EndorseBlockId]
endorseBlocksToVoteFor cfg slot ibs ebs =
  let cond = shouldVoteOnEB cfg slot ibs
   in map (.id) . filter cond $
        maybe [] ebs.validEndorseBlocks (stageRange cfg Vote slot Endorse)

-----------------------------------------------------------------
---- Expected generation rates in each slot.
-----------------------------------------------------------------

newtype NetworkRate = NetworkRate Double
newtype NodeRate = NodeRate Double
newtype StakeFraction = StakeFraction Double

splitIntoSubSlots :: NetworkRate -> [NetworkRate]
splitIntoSubSlots (NetworkRate r)
  | r <= 1 = [NetworkRate r]
  | otherwise =
      let
        q = ceiling r
        fq = NetworkRate $ r / fromIntegral q
       in
        replicate q fq

inputBlockRate :: LeiosConfig -> SlotNo -> [NetworkRate]
inputBlockRate cfg@LeiosConfig{inputBlockFrequencyPerSlot} slot =
  assert (isStage cfg Propose slot) $
    splitIntoSubSlots $
      NetworkRate inputBlockFrequencyPerSlot

endorseBlockRate :: LeiosConfig -> SlotNo -> [NetworkRate]
endorseBlockRate cfg slot = fromMaybe [] $ do
  guard $ isStage cfg Endorse slot
  startEndorse <- stageStart cfg Endorse slot Endorse
  guard $ startEndorse == slot
  return $ splitIntoSubSlots $ NetworkRate cfg.endorseBlockFrequencyPerStage

-- TODO: double check with technical report section on voting when ready.
votingRate :: LeiosConfig -> SlotNo -> [NetworkRate]
votingRate cfg slot = fromMaybe [] $ do
  guard $ isStage cfg Vote slot
  range <- stageRange cfg Vote slot Vote
  guard $ slot `inRange` rangePrefix cfg.activeVotingStageLength range
  let votingFrequencyPerSlot = cfg.votingFrequencyPerStage / fromIntegral cfg.activeVotingStageLength
  return $ splitIntoSubSlots $ NetworkRate votingFrequencyPerSlot

-- mostly here to showcase the types.
nodeRate :: StakeFraction -> NetworkRate -> NodeRate
nodeRate (StakeFraction s) (NetworkRate r) = NodeRate (s * r)
