{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Short where

import Control.Exception (assert)
import Control.Monad (guard)
import Data.Set (Set)
import qualified Data.Set as Set
import LeiosProtocol.Common
import ModelTCP
import Ouroboros.Network.AnchoredFragment (Anchor)
import Prelude hiding (id)

data SizesConfig = SizesConfig
  { producerId :: Bytes
  , vrfProof :: Bytes
  , signature_ :: Bytes
  , reference :: Bytes
  -- ^ size of a block reference, presumably hash
  , voteCrypto :: Bytes
  -- ^ voting is in flux, we stay flexible (atm it's two signatures)
  , certificate :: Certificate -> Bytes
  -- ^ certificate size might depend on number of votes.
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
  -- TODO: validation times and max sizes parameters.
  }

class FixSize a where
  fixSize :: LeiosConfig -> a -> a

instance FixSize InputBlockHeader where
  fixSize cfg ib@InputBlockHeader{..} =
    InputBlockHeader
      { size =
          cfg.sizes.producerId
            + messageSizeBytes ib.slot
            + subSlotSize
            + cfg.sizes.reference {- ib.rankingBlock -}
            + 32 {- hash of body -}
            + cfg.sizes.vrfProof
            + cfg.sizes.signature_
      , ..
      }
   where
    subSlotSize =
      if cfg.inputBlockFrequencyPerSlot > 1
        then messageSizeBytes ib.subSlot
        else
          0

instance FixSize EndorseBlock where
  fixSize cfg eb@EndorseBlock{..} =
    EndorseBlock
      { size =
          cfg.sizes.producerId
            + messageSizeBytes eb.slot
            + cfg.sizes.reference
              * fromIntegral
                ( length eb.inputBlocks
                    + length eb.endorseBlocksEarlierStage
                    + length eb.endorseBlocksEarlierPipeline
                )
            + cfg.sizes.vrfProof
            + cfg.sizes.signature_
      , ..
      }

instance FixSize VoteMsg where
  fixSize cfg v@VoteMsg{..} =
    VoteMsg
      { size =
          cfg.sizes.producerId
            + messageSizeBytes v.slot
            + cfg.sizes.reference {- EB ref -}
            + cfg.sizes.voteCrypto
      , ..
      }

instance FixSize RankingBlockBody where
  fixSize cfg rb@RankingBlockBody{..} =
    RankingBlockBody
      { size =
          sum [cfg.sizes.reference + cfg.sizes.certificate cert | (_, cert) <- rb.endorseBlocks]
            + rb.payload
      , ..
      }

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
  (SlotNo, SlotNo)
stageRange cfg = stageRange' cfg.sliceLength

stageRange' :: Int -> Stage -> SlotNo -> Stage -> (SlotNo, SlotNo)
stageRange' l s0 slot s = slice l slot (fromEnum s0 - fromEnum s)

stageRange'_prop :: Int -> SlotNo -> Bool
stageRange'_prop l slot =
  and [slot `inRange` stageRange' l stage slot stage | stage <- stages]
    && and [contiguous $ map (stageRange' l stage slot) stages | stage <- stages]
 where
  stages = [minBound .. maxBound]
  rightSize (a, b) = length [a .. b] == l
  contiguous (x : y : xs) = rightSize x && succ (snd x) == fst y && contiguous (y : xs)
  contiguous _ = True

stageEnd :: LeiosConfig -> Stage -> SlotNo -> Stage -> SlotNo
stageEnd l s0 slot s = snd $ stageRange l s0 slot s

stageStart :: LeiosConfig -> Stage -> SlotNo -> Stage -> SlotNo
stageStart l s0 slot s = fst $ stageRange l s0 slot s

----------------------------------------------------------------------------------------------
---- Smart constructors
----------------------------------------------------------------------------------------------

mkRankingBlockBody :: LeiosConfig -> EndorseBlockId -> Certificate -> Bytes -> RankingBlockBody
mkRankingBlockBody cfg eb cert payload =
  fixSize cfg $
    RankingBlockBody
      { endorseBlocks = [(eb, cert)]
      , payload
      , size = 0
      }

mkInputBlockHeader ::
  LeiosConfig ->
  InputBlockId ->
  SlotNo ->
  SubSlotNo ->
  NodeId ->
  RankingBlockId ->
  InputBlockHeader
mkInputBlockHeader cfg id slot subSlot producer rankingBlock =
  fixSize cfg $ InputBlockHeader{size = 0, ..}

mkInputBlock :: LeiosConfig -> InputBlockHeader -> Bytes -> InputBlock
mkInputBlock _cfg header bodySize =
  InputBlock{header, body = InputBlockBody{id = header.id, size = bodySize}}

mkEndorseBlock ::
  LeiosConfig -> EndorseBlockId -> SlotNo -> NodeId -> [InputBlockId] -> EndorseBlock
mkEndorseBlock cfg id slot producer inputBlocks =
  -- Endorse blocks are produced at the beginning of the stage.
  assert (stageStart cfg Endorse slot Endorse == slot) $
    fixSize cfg $
      EndorseBlock{endorseBlocksEarlierStage = [], endorseBlocksEarlierPipeline = [], size = 0, ..}

mkVoteMsg :: LeiosConfig -> VoteId -> SlotNo -> NodeId -> EndorseBlockId -> VoteMsg
mkVoteMsg cfg id slot producer endorseBlock = fixSize cfg $ VoteMsg{size = 0, ..}

mkCertificate :: LeiosConfig -> Set VoteId -> Certificate
mkCertificate cfg vs = assert (Set.size vs <= cfg.votesForCertificate) $ Certificate vs

---------------------------------------------------------------------------------------
---- Selecting data to build blocks
---------------------------------------------------------------------------------------

-- Buffers views, divided to avoid reading in unneeded buffers.

data NewRankingBlockData = NewRankingBlockData
  { freshestCertifiedEB :: (EndorseBlockId, Certificate)
  , txsPayload :: Bytes
  , headAnchor :: Anchor RankingBlock
  }

data NewInputBlockData = NewInputBlockData
  { referenceRankingBlock :: RankingBlockId
  , txsPayload :: Bytes
  }

data InputBlocksSnapshot = InputBlocksSnapshot
  { validInputBlocks :: InputBlocksQuery -> [InputBlockId]
  }

data EndorseBlocksSnapshot = EndorseBlocksSnapshot
  { validEndorseBlocks :: (SlotNo, SlotNo) -> [EndorseBlock]
  }

-- | Both constraints are inclusive.
data InputBlocksQuery = InputBlocksQuery
  { generatedBetween :: (SlotNo, SlotNo)
  , receivedBy :: SlotNo
  }

inputBlocksToEndorse ::
  LeiosConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  [InputBlockId]
inputBlocksToEndorse cfg current buffer =
  buffer.validInputBlocks
    InputBlocksQuery
      { generatedBetween = stageRange cfg Endorse current Propose
      , receivedBy = stageEnd cfg Endorse current Deliver2
      }

shouldVoteOnEB ::
  LeiosConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  EndorseBlock ->
  Bool
shouldVoteOnEB cfg slot buffers = cond
 where
  generatedBetween = stageRange cfg Vote slot Propose
  receivedByEndorse =
    buffers.validInputBlocks
      InputBlocksQuery
        { generatedBetween
        , receivedBy = stageEnd cfg Vote slot Endorse
        }
  receivedByDeliver1 = buffers.validInputBlocks q
   where
    q =
      InputBlocksQuery
        { generatedBetween
        , receivedBy = stageEnd cfg Vote slot Deliver1
        }
  -- TODO: use sets in EndorseBlock?
  subset xs ys = all (`elem` ys) xs

  cond :: EndorseBlock -> Bool
  cond eb = assert assumptions $ acd && b
   where
    assumptions =
      null eb.endorseBlocksEarlierStage
        && null eb.endorseBlocksEarlierPipeline
        && eb.slot `inRange` stageRange cfg Vote slot Endorse
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
        ebs.validEndorseBlocks (stageRange cfg Vote slot Endorse)

-----------------------------------------------------------------
---- Expected generation rates in each slot.
-----------------------------------------------------------------

newtype NetworkRate = NetworkRate Double
newtype NodeRate = NodeRate Double
newtype StakeFraction = StakeFraction Double

-- | Note: each SubSlot rate is `<= 1` by construction.
inputBlockRate :: LeiosConfig -> SlotNo -> [(SubSlotNo, NetworkRate)]
inputBlockRate LeiosConfig{inputBlockFrequencyPerSlot} _slot
  | inputBlockFrequencyPerSlot <= 1 = [(0, NetworkRate inputBlockFrequencyPerSlot)]
  | otherwise =
      let q = ceiling inputBlockFrequencyPerSlot
          fq = NetworkRate $ inputBlockFrequencyPerSlot / fromIntegral q
       in map (,fq) [0 .. toEnum (q - 1)]

-- | Note: if the NodeRate ends up `>= 1`, you still only produce one block.
endorseBlockRate :: LeiosConfig -> SlotNo -> Maybe NetworkRate
endorseBlockRate cfg slot = do
  guard $ stageStart cfg Endorse slot Endorse == slot
  return $ NetworkRate cfg.endorseBlockFrequencyPerStage

-- | TODO: a little unclear what to do if the NodeRate is `>= 1`.
votingRate :: LeiosConfig -> SlotNo -> Maybe NetworkRate
votingRate cfg slot = do
  guard $ slot `inRange` rangePrefix cfg.activeVotingStageLength (stageRange cfg Vote slot Vote)
  return $ NetworkRate $ cfg.votingFrequencyPerStage / fromIntegral cfg.activeVotingStageLength

-- mostly here to showcase the types.
nodeRate :: StakeFraction -> NetworkRate -> NodeRate
nodeRate (StakeFraction s) (NetworkRate r) = NodeRate (s * r)
