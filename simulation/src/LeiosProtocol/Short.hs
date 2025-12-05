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
import Control.DeepSeq
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
import qualified PraosProtocol.Common.Chain as Chain
import Statistics.Distribution
import Statistics.Distribution.Poisson
import Prelude hiding (id)

-- | The sizes here are prescriptive, used to fill in fields that MessageSize will read from.
data SizesConfig = SizesConfig
  { inputBlockHeader :: !Bytes
  , inputBlockBodyAvgSize :: !Bytes
  -- ^ as we do not model transactions we just use a fixed size for bodies.
  , inputBlockBodyMaxSize :: !Bytes
  , endorseBlockBodyAvgSize :: !Bytes
  -- ^ unused by Short/Full Leios, used by Linear Leios eg
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
  , linearEndorseBlockGeneration :: !(InputBlock -> DiffTime)
  , linearEndorseBlockValidation :: !(InputBlock -> DiffTime)
  , voteMsgGeneration :: !(VoteMsg -> [EndorseBlock] -> DiffTime)
  , linearVoteMsgGeneration :: !(VoteMsg -> [InputBlock] -> DiffTime)
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

data LeiosConfig
  = forall p.
  IsPipeline p =>
  LeiosConfig
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
  , maxEndorseBlockAgeSlots :: Int
  -- ^ maximum age of a certified endorsement block before it expires
  , maxEndorseBlockAgeForRelaySlots :: Int
  -- ^ maximum age of an uncertified endorsement block before it expires
  , cleanupPolicies :: CleanupPolicies
  -- ^ active cleanup policies
  , variant :: LeiosVariant
  , headerDiffusionTime :: NominalDiffTime
  -- ^ Δ_{hdr}.
  , lateIbInclusion :: Bool
  -- ^ Whether an EB also includes IBs from the two previous iterations.
  --
  -- TODO Merely one previous iteration if 'pipeline' is 'SingleVote'?
  , pipelinesToReferenceFromEB :: Int
  -- ^ how many older pipelines to reference from an EB when `variant = Full`.
  , votingFrequencyPerStage :: Double
  , voteSendStage :: Stage p
  , votesForCertificate :: Int
  , sizes :: SizesConfig
  , delays :: LeiosDelays
  , linearVoteStageLengthSlots :: Int
  , linearDiffuseStageLengthSlots :: Int
  , ibDiffusion :: RelayDiffusionConfig
  , ebDiffusion :: RelayDiffusionConfig
  , voteDiffusion :: RelayDiffusionConfig
  , relayStrategy :: RelayStrategy
  }

data SomeStage = forall p. IsPipeline p => SomeStage (SingPipeline p) (Stage p)

convertConfig :: OnDisk.Config -> LeiosConfig
convertConfig disk =
  ( if disk.treatBlocksAsFull
      then delaysAndSizesAsFull
      else (\x -> x)
  )
    $ case voting of
      SomeStage pipeline voteSendStage -> do
        let sliceLength = fromIntegral disk.leiosStageLengthSlots
        LeiosConfig
          { praos
          , pipeline
          , voteSendStage
          , sliceLength
          , inputBlockFrequencyPerSlot = disk.ibGenerationProbability
          , endorseBlockFrequencyPerStage = disk.ebGenerationProbability
          , maxEndorseBlockAgeSlots = fromIntegral disk.ebMaxAgeSlots
          , maxEndorseBlockAgeForRelaySlots = fromIntegral disk.ebMaxAgeForRelaySlots
          , cleanupPolicies = disk.cleanupPolicies
          , variant = disk.leiosVariant
          , headerDiffusionTime = realToFrac $ durationMsToDiffTime disk.leiosHeaderDiffusionTimeMs
          , lateIbInclusion = disk.leiosLateIbInclusion
          , pipelinesToReferenceFromEB =
              case disk.leiosVariant of
                Full -> ceiling ((3 * disk.praosChainQuality) / fromIntegral sliceLength) - 2
                Short -> 0
                Linear -> 0
          , activeVotingStageLength = fromIntegral disk.leiosStageActiveVotingSlots
          , linearVoteStageLengthSlots = fromIntegral disk.linearVoteStageLengthSlots
          , linearDiffuseStageLengthSlots = fromIntegral disk.linearDiffuseStageLengthSlots
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
  forEach n xs = n * fromIntegral (length @[] xs)
  forEachKey n m = n * fromIntegral (Map.size m)
  durationMsToDiffTime (DurationMs d) = secondsToDiffTime $ d / 1000
  voting =
    if disk.leiosVoteSendRecvStages
      then SomeStage SingSplitVote VoteSend
      else SomeStage SingSingleVote Vote
  praos =
    PraosConfig
      { blockFrequencyPerSlot = disk.rbGenerationProbability
      , headerSize = fromIntegral disk.rbHeadSizeBytes
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
      , headerValidationDelay = const $ durationMsToDiffTime disk.rbHeadValidationCpuTimeMs
      , blockGenerationDelay = \(Block _ body) ->
          durationMsToDiffTime disk.rbGenerationCpuTimeMs
            + sum (map (certificateGeneration . snd) body.endorseBlocks)
      , configureConnection = mkConnectionConfig (tcpCongestionControl disk) (multiplexMiniProtocols disk)
      , relayStrategy = disk.relayStrategy
      }
  certificateSize (Certificate votesMap) =
    fromIntegral $
      disk.certSizeBytesConstant
        + disk.certSizeBytesPerNode
          `forEachKey` votesMap
  sizes =
    SizesConfig
      { inputBlockHeader = fromIntegral disk.ibHeadSizeBytes
      , inputBlockBodyAvgSize = fromIntegral disk.ibBodyAvgSizeBytes
      , inputBlockBodyMaxSize = fromIntegral disk.ibBodyMaxSizeBytes
      , endorseBlockBodyAvgSize = fromIntegral disk.ebBodyAvgSizeBytes
      , endorseBlock = \eb ->
          fromIntegral $
            disk.ebSizeBytesConstant
              + disk.ebSizeBytesPerIb
                `forEach` eb.inputBlocks
              -- TODO: make it a per-ref field.
              + disk.ebSizeBytesPerIb
                `forEach` eb.endorseBlocksEarlierPipeline
      , voteMsg = \vt ->
          fromIntegral $
            disk.voteBundleSizeBytesConstant
              + disk.voteBundleSizeBytesPerEb
                `forEach` vt.endorseBlocks
      , certificate = \_cert ->
          fromIntegral $
            assert (0 == disk.certSizeBytesPerNode) $ -- TODO
              disk.certSizeBytesConstant
      , rankingBlockLegacyPraosPayloadAvgSize = fromIntegral disk.rbBodyLegacyPraosPayloadAvgSizeBytes
      }
  certificateGeneration (Certificate votesMap) =
    durationMsToDiffTime $
      disk.certGenerationCpuTimeMsConstant
        + disk.certGenerationCpuTimeMsPerNode
          `forEachKey` votesMap
  certificateValidation (Certificate votesMap) =
    durationMsToDiffTime $
      disk.certValidationCpuTimeMsConstant
        + disk.certValidationCpuTimeMsPerNode
          `forEachKey` votesMap
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
      , linearEndorseBlockGeneration = const $ durationMsToDiffTime disk.ebGenerationCpuTimeMs
      , linearEndorseBlockValidation = \ib ->
          durationMsToDiffTime $
            disk.ebBodyValidationCpuTimeMsConstant
              + disk.ebBodyValidationCpuTimeMsPerByte * fromIntegral ib.body.size
      , -- TODO: can parallelize?
        voteMsgGeneration = \vm ebs ->
          assert (vm.endorseBlocks == map (.id) ebs) $
            durationMsToDiffTime $
              sum
                [ disk.voteGenerationCpuTimeMsConstant
                    + disk.voteGenerationCpuTimeMsPerIb
                      `forEach` eb.inputBlocks
                | eb <- ebs
                ]
      , linearVoteMsgGeneration = \vm ibs ->
          assert (1 == length vm.endorseBlocks) $
            assert (vm.endorseBlocks == map (convertLinearId . (.id)) ibs) $
              assert (0 == disk.voteGenerationCpuTimeMsPerTx) $ -- TODO
                durationMsToDiffTime $
                  disk.voteGenerationCpuTimeMsConstant `forEach` ibs
      , voteMsgValidation = \vm ->
          durationMsToDiffTime $
            disk.voteValidationCpuTimeMs `forEach` vm.endorseBlocks
      , certificateGeneration = const $ error "certificateGeneration delay included in RB generation"
      , certificateValidation = const $ error "certificateValidation delay included in RB validation"
      }

convertLinearId :: InputBlockId -> EndorseBlockId
convertLinearId (InputBlockId x y) = EndorseBlockId x y

unconvertLinearId :: EndorseBlockId -> InputBlockId
unconvertLinearId (EndorseBlockId x y) = InputBlockId x y

delaysAndSizesAsFull :: LeiosConfig -> LeiosConfig
delaysAndSizesAsFull cfg@LeiosConfig{pipeline, voteSendStage} =
  -- Fields spelled out to more likely trigger an error and review when type changes.
  LeiosConfig
    { praos
    , sizes
    , delays
    , pipeline = pipeline
    , sliceLength = cfg.sliceLength
    , inputBlockFrequencyPerSlot = cfg.inputBlockFrequencyPerSlot
    , endorseBlockFrequencyPerStage = cfg.endorseBlockFrequencyPerStage
    , maxEndorseBlockAgeSlots = cfg.maxEndorseBlockAgeSlots
    , maxEndorseBlockAgeForRelaySlots = fromIntegral cfg.maxEndorseBlockAgeForRelaySlots
    , cleanupPolicies = cfg.cleanupPolicies
    , variant = cfg.variant
    , headerDiffusionTime = cfg.headerDiffusionTime
    , lateIbInclusion = cfg.lateIbInclusion
    , pipelinesToReferenceFromEB = cfg.pipelinesToReferenceFromEB
    , activeVotingStageLength = cfg.activeVotingStageLength
    , linearVoteStageLengthSlots = cfg.linearVoteStageLengthSlots
    , linearDiffuseStageLengthSlots = cfg.linearDiffuseStageLengthSlots
    , votingFrequencyPerStage = cfg.votingFrequencyPerStage
    , voteSendStage = voteSendStage
    , votesForCertificate = cfg.votesForCertificate
    , ibDiffusion = cfg.ibDiffusion
    , ebDiffusion = cfg.ebDiffusion
    , voteDiffusion = cfg.voteDiffusion
    , relayStrategy = cfg.relayStrategy
    }
 where
  fullIB = mockFullInputBlock cfg
  fullEB = mockFullEndorseBlock cfg
  fullVT = mockFullVoteMsg cfg
  fullEBsVotedFor =
    [ EndorseBlock{id = id', ..}
    | id' <- fullVT.endorseBlocks
    , let EndorseBlock{..} = fullEB
    ]
  fullLinearEBsVotedFor =
    [ InputBlock
        { body = fullIB.body
        , header =
            let InputBlockHeader{..} = fullIB.header
             in InputBlockHeader{id = unconvertLinearId id', ..}
        }
    | id' <- fullVT.endorseBlocks
    ]
  fullRB = mockFullRankingBlock cfg
  fullCert = mockFullCertificate cfg
  praos =
    PraosConfig
      { blockFrequencyPerSlot = cfg.praos.blockFrequencyPerSlot
      , blockValidationDelay = const @DiffTime $ cfg.praos.blockValidationDelay fullRB
      , headerValidationDelay = const @DiffTime $ cfg.praos.headerValidationDelay fullRB.blockHeader
      , blockGenerationDelay = const @DiffTime $ cfg.praos.blockGenerationDelay fullRB
      , headerSize = cfg.praos.headerSize :: Bytes
      , bodySize = const @Bytes $ cfg.praos.bodySize fullRB.blockBody
      , bodyMaxSize = cfg.praos.bodyMaxSize
      , configureConnection = cfg.praos.configureConnection
      , relayStrategy = cfg.praos.relayStrategy
      }
  sizes =
    SizesConfig
      { inputBlockHeader = cfg.sizes.inputBlockHeader :: Bytes
      , inputBlockBodyAvgSize = cfg.sizes.inputBlockBodyAvgSize :: Bytes
      , inputBlockBodyMaxSize = cfg.sizes.inputBlockBodyMaxSize :: Bytes
      , endorseBlockBodyAvgSize = cfg.sizes.endorseBlockBodyAvgSize :: Bytes
      , endorseBlock = const @Bytes $ cfg.sizes.endorseBlock $ mockFullEndorseBlock cfg
      , voteMsg = const @Bytes $ cfg.sizes.voteMsg $ mockFullVoteMsg cfg
      , certificate = const @Bytes $ cfg.sizes.certificate $ mockFullCertificate cfg
      , rankingBlockLegacyPraosPayloadAvgSize = cfg.sizes.rankingBlockLegacyPraosPayloadAvgSize
      }
  delays =
    LeiosDelays
      { inputBlockGeneration = const @DiffTime $ cfg.delays.inputBlockGeneration fullIB
      , inputBlockHeaderValidation = const @DiffTime $ cfg.delays.inputBlockHeaderValidation $ fullIB.header
      , inputBlockValidation = const @DiffTime $ cfg.delays.inputBlockValidation fullIB
      , endorseBlockGeneration = const @DiffTime $ cfg.delays.endorseBlockGeneration fullEB
      , endorseBlockValidation = const @DiffTime $ cfg.delays.endorseBlockValidation fullEB
      , linearEndorseBlockGeneration = const @DiffTime $ cfg.delays.linearEndorseBlockGeneration fullIB
      , linearEndorseBlockValidation = const @DiffTime $ cfg.delays.linearEndorseBlockValidation fullIB
      , voteMsgGeneration =
          const $
            const @DiffTime $
              cfg.delays.voteMsgGeneration
                fullVT
                fullEBsVotedFor
      , linearVoteMsgGeneration =
          const $
            const @DiffTime $
              cfg.delays.linearVoteMsgGeneration
                fullVT
                fullLinearEBsVotedFor
      , voteMsgValidation = const @DiffTime $ cfg.delays.voteMsgValidation fullVT
      , certificateGeneration = const @DiffTime $ cfg.delays.certificateGeneration fullCert
      , certificateValidation = const @DiffTime $ cfg.delays.certificateValidation fullCert
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
  Propose :: Stage a
  Deliver1 :: Stage a
  Deliver2 :: Stage a
  Endorse :: Stage a
  Vote :: Stage SingleVote
  VoteSend :: Stage SplitVote
  VoteRecv :: Stage SplitVote

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

inRange :: Ord a => a -> (a, a) -> Bool
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

pipelineMonus :: PipelineNo -> Word64 -> PipelineNo
pipelineMonus (PipelineNo w) i = PipelineNo $ w - min w i

stageRangeOf :: forall p. IsPipeline p => LeiosConfig -> PipelineNo -> Stage p -> (SlotNo, SlotNo)
stageRangeOf cfg pl stage =
  fromMaybe
    undefined
    (stageRange cfg minBound (toEnum (fromEnum pl * cfg.sliceLength)) stage)

-- | WARNING This fails if the slot is earlier than the beginning of the stage
-- in the first iteration (ie @'PipelineNo' 0@)
pipelineOf :: forall p. IsPipeline p => LeiosConfig -> Stage p -> SlotNo -> PipelineNo
pipelineOf cfg stage sl =
  maybe err cnv $ stageStart cfg stage sl minBound
 where
  cnv = toEnum . (`div` cfg.sliceLength) . fromEnum

  err = error $ show (cfg.sliceLength, x, stage, sl)

  x :: String
  x = case cfg of
    LeiosConfig{pipeline} -> case pipeline of
      SingSingleVote -> "SingleVote"
      SingSplitVote -> "SplitVote"

forEachPipeline :: (forall p. Stage p) -> (forall p. IsPipeline p => Stage p -> a) -> [a]
forEachPipeline s k = [k @SingleVote s, k @SplitVote s]

lastEndorse :: LeiosConfig -> PipelineNo -> SlotNo
lastEndorse leios@LeiosConfig{pipeline = _ :: SingPipeline p} pipelineNo =
  snd $ stageRangeOf @p leios pipelineNo Endorse

lastVoteSend :: LeiosConfig -> PipelineNo -> SlotNo
lastVoteSend leios@LeiosConfig{pipeline} pipelineNo = case pipeline of
  SingSingleVote -> snd (stageRangeOf leios pipelineNo Vote)
  SingSplitVote -> snd (stageRangeOf leios pipelineNo VoteSend)

lastVoteRecv :: LeiosConfig -> PipelineNo -> SlotNo
lastVoteRecv leios@LeiosConfig{pipeline} pipelineNo = case pipeline of
  SingSingleVote -> snd (stageRangeOf leios pipelineNo Vote)
  SingSplitVote -> snd (stageRangeOf leios pipelineNo VoteRecv)

endorseRange :: LeiosConfig -> PipelineNo -> (SlotNo, SlotNo)
endorseRange cfg@LeiosConfig{pipeline = (_ :: SingPipeline p)} p =
  stageRangeOf @p cfg p Endorse

proposeRange :: LeiosConfig -> PipelineNo -> (SlotNo, SlotNo)
proposeRange cfg@LeiosConfig{pipeline = (_ :: SingPipeline p)} p =
  stageRangeOf @p cfg p Propose

pipelineRange :: LeiosConfig -> PipelineNo -> (SlotNo, SlotNo)
pipelineRange cfg p = (fst $ proposeRange cfg p, lastVoteRecv cfg p)

endorseBlockPipeline :: LeiosConfig -> EndorseBlock -> PipelineNo
endorseBlockPipeline cfg@LeiosConfig{pipeline = _ :: SingPipeline p} eb = pipelineOf @p cfg Endorse eb.slot

inputBlockPipeline :: LeiosConfig -> InputBlock -> PipelineNo
inputBlockPipeline cfg@LeiosConfig{pipeline = _ :: SingPipeline p} ib = pipelineOf @p cfg Propose ib.header.slot

voteMsgPipeline :: LeiosConfig -> VoteMsg -> PipelineNo
voteMsgPipeline cfg@LeiosConfig{voteSendStage} vt = pipelineOf cfg voteSendStage vt.slot

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

mkEndorseBlock ::
  LeiosConfig -> EndorseBlockId -> SlotNo -> NodeId -> [EndorseBlockId] -> [InputBlockId] -> EndorseBlock
mkEndorseBlock cfg@LeiosConfig{pipeline = _ :: SingPipeline p} id slot producer endorseBlocksEarlierPipeline inputBlocks =
  assert
    ( (cfg.variant == Full && length endorseBlocksEarlierPipeline <= cfg.pipelinesToReferenceFromEB)
        || null endorseBlocksEarlierPipeline
    )
    $
    -- Endorse blocks are produced at the beginning of the stage.
    assert (stageStart @p cfg Endorse slot Endorse == Just slot)
    $ rnf endorseBlocksEarlierPipeline
    `seq` rnf inputBlocks
    `seq` fixSize
      cfg
      EndorseBlock{endorseBlocksEarlierStage = [], size = 0, ..}

mockEndorseBlock :: LeiosConfig -> Int -> EndorseBlock
mockEndorseBlock cfg n =
  assert (cfg.variant /= Full) $
    mkEndorseBlock
      cfg
      (EndorseBlockId (NodeId 0) 0)
      0
      (NodeId 0)
      []
      [InputBlockId (NodeId 0) i | i <- [0 .. n - 1]]

mockFullEndorseBlock :: LeiosConfig -> EndorseBlock
mockFullEndorseBlock cfg = mockEndorseBlock cfg $ cfg.sliceLength * (ceiling cfg.inputBlockFrequencyPerSlot)

mkVoteMsg :: LeiosConfig -> VoteId -> SlotNo -> NodeId -> Word64 -> [EndorseBlockId] -> VoteMsg
mkVoteMsg cfg id slot producer votes endorseBlocks = fixSize cfg $ VoteMsg{size = 0, ..}

mkCertificate :: LeiosConfig -> Map VoteId Word64 -> Certificate
mkCertificate cfg vs =
  assert (fromIntegral cfg.votesForCertificate <= sum (Map.elems vs)) $
    Certificate vs

mockRankingBlock :: LeiosConfig -> Int -> RankingBlock
mockRankingBlock cfg n =
  fixSize cfg $
    fixupBlock (Chain.headAnchor @RankingBlock Genesis) $
      mkPartialBlock 0 $
        mkRankingBlockBody
          cfg
          (NodeId 0)
          (Just (EndorseBlockId (NodeId 0) 0, mockCertificate cfg n))
          cfg.sizes.rankingBlockLegacyPraosPayloadAvgSize

mockFullRankingBlock :: LeiosConfig -> RankingBlock
mockFullRankingBlock cfg =
  fixSize cfg $
    fixupBlock (Chain.headAnchor @RankingBlock Genesis) $
      mkPartialBlock 0 $
        mkRankingBlockBody
          cfg
          (NodeId 0)
          (Just (EndorseBlockId (NodeId 0) 0, mockFullCertificate cfg))
          cfg.sizes.rankingBlockLegacyPraosPayloadAvgSize

mockFullInputBlock :: LeiosConfig -> InputBlock
mockFullInputBlock cfg =
  mkInputBlock
    cfg
    (mkInputBlockHeader cfg (InputBlockId (NodeId 0) 0) 0 0 (NodeId 0) GenesisHash)
    cfg.sizes.inputBlockBodyAvgSize

mockFullVoteMsg :: LeiosConfig -> VoteMsg
mockFullVoteMsg cfg =
  mkVoteMsg
    cfg
    (VoteId (NodeId 0) 0)
    0
    (NodeId 0)
    1
    [EndorseBlockId (NodeId 0) i | i <- [0 .. ceiling cfg.endorseBlockFrequencyPerStage - 1]]

mockCertificate :: LeiosConfig -> Int -> Certificate
mockCertificate cfg n =
  mkCertificate
    cfg
    ( Map.fromList $
        [ (VoteId (NodeId 0) i, 1)
        | i <-
            [ 0
            .. n - 1
            ]
        ]
    )

mockFullCertificate :: LeiosConfig -> Certificate
mockFullCertificate cfg = mockCertificate cfg cfg.votesForCertificate

---------------------------------------------------------------------------------------
---- Selecting data to build blocks
---------------------------------------------------------------------------------------

-- Buffers views, divided to avoid reading unneeded buffers.

data NewRankingBlockData = NewRankingBlockData
  { prevChain :: Chain RankingBlock
  , mbEbCert :: Maybe (EndorseBlockId, Certificate)
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

data EndorseBlocksSnapshot = EndorseBlocksSnapshot
  { validEndorseBlocks :: (SlotNo, SlotNo) -> [EndorseBlock]
  , certifiedEndorseBlocks :: (PipelineNo, PipelineNo) -> [(PipelineNo, [(EndorseBlock, Certificate, UTCTime)])]
  }

-- | In which contemporary stage was an IB delivered
--
-- IBs cannot be deliver earlier than any of these options, due to the
-- 'LeiosProtocol.Relay.shouldNotRequest' logic of the
-- 'LeiosProtocol.Short.Node.relayIBState'.
--
-- IBs that are delivered later than any of these options are discarded,
-- ignored.
data IbDeliveryStage
  = -- | The node will not vote for an EB that excludes IBs that arrived during
    -- Propose or Deliver1.
    --
    -- The node will include IBs that arrived during Propose or Deliver1 in an
    -- EB it makes.
    IbDuringProposeOrDeliver1
  | -- | The node will include IBs that arrived during Deliver2 in an EB it makes.
    IbDuringDeliver2
  | -- | The node will not vote for an EB that includes IBs that arrived later
    -- than Endorse.
    IbDuringEndorse
  deriving (Bounded, Enum, Eq, Ord, Show)

-- | Both constraints are inclusive.
data InputBlocksQuery = InputBlocksQuery
  { generatedBetween :: (PipelineNo, PipelineNo)
  , receivedBy :: IbDeliveryStage
  -- ^ This is checked against time the body is downloaded, before validation.
  }

ibWasDeliveredLate :: LeiosConfig -> SlotConfig -> SlotNo -> UTCTime -> Bool
ibWasDeliveredLate cfg slotCfg sl deliveryTime =
  case ibDeliveryStage cfg slotCfg sl deliveryTime of
    Nothing -> True
    Just{} -> False

ibDeliveryStage :: LeiosConfig -> SlotConfig -> SlotNo -> UTCTime -> Maybe IbDeliveryStage
ibDeliveryStage
  cfg@LeiosConfig{pipeline = _ :: SingPipeline p}
  slotCfg
  ibSlot
  deliveryTime
    | before loPropose = Nothing -- TODO future blocks?
    | before loDeliver2 = Just IbDuringProposeOrDeliver1
    | before loEndorse = Just IbDuringDeliver2
    | before (succ hiEndorse) = Just IbDuringEndorse
    | otherwise = Nothing -- TODO late blocks?
   where
    p = pipelineOf @p cfg Propose ibSlot

    before sl = deliveryTime < slotTime slotCfg sl

    (loPropose, _) = stageRangeOf @p cfg p Propose
    (loDeliver2, _) = stageRangeOf @p cfg p Deliver2
    (loEndorse, hiEndorse) = stageRangeOf @p cfg p Endorse

inputBlocksToEndorse ::
  LeiosConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  [InputBlockId]
inputBlocksToEndorse cfg@LeiosConfig{pipeline = _ :: SingPipeline p} current buffer =
  buffer.validInputBlocks
    InputBlocksQuery
      { generatedBetween = (lo, hi)
      , receivedBy = IbDuringDeliver2
      }
 where
  hi = pipelineOf @p cfg Endorse current
  lo = if cfg.lateIbInclusion then pipelineMonus hi 2 else hi

-- | Returns possible EBs to reference from current pipeline EB.
endorseBlocksToReference ::
  LeiosConfig ->
  PipelineNo ->
  EndorseBlocksSnapshot ->
  (PipelineNo -> UTCTime -> Bool) ->
  [(PipelineNo, [EndorseBlock])]
endorseBlocksToReference cfg pl EndorseBlocksSnapshot{..} checkDeliveryTime
  | Full <- cfg.variant =
      assert
        ( all (\(p, ebs) -> all (\eb -> p == endorseBlockPipeline cfg eb) ebs && succ (succ p) <= pl) result
            && (\ps -> sort ps == ps) (map fst result)
        )
        result
  | otherwise = []
 where
  result =
    [ (p, [eb | (eb, _, _) <- es])
    | plRange <- maybeToList $ pipelinesToReferenceFromEB cfg pl
    , (p, es) <- certifiedEndorseBlocks plRange
    , or [checkDeliveryTime p t | (_, _, t) <- es]
    ]

pipelinesToReferenceFromEB :: LeiosConfig -> PipelineNo -> Maybe (PipelineNo, PipelineNo)
pipelinesToReferenceFromEB cfg pl
  | Full <- cfg.variant = do
      let n = cfg.pipelinesToReferenceFromEB
      predPl <- safePred pl
      case fromEnum predPl - maxStagesAfterEndorse of
        newestIx
          | newestIx < 0 -> Nothing
          | otherwise ->
              Just
                ( toEnum $ max 0 $ newestIx - (n - 1)
                , toEnum newestIx
                )
  | otherwise = Nothing
 where
  maxStagesAfterEndorse = 2
  safePred x = do
    guard $ x > minBound
    pure $ pred x

shouldVoteOnEB ::
  LeiosConfig ->
  SlotConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  EndorseBlocksSnapshot ->
  EndorseBlock ->
  Bool
shouldVoteOnEB cfg@LeiosConfig{voteSendStage} _ slot _buffers _
  -- checks whether a pipeline has been started before.
  | Nothing <- stageRange cfg voteSendStage slot Propose = const False
shouldVoteOnEB cfg@LeiosConfig{voteSendStage = voteSendStage :: Stage p} slotConfig slot buffers ebuffers = cond
 where
  generatedBetween = (lo, hi)
   where
    hi = pipelineOf @p cfg voteSendStage slot
    lo = if cfg.lateIbInclusion then pipelineMonus hi 2 else hi
  receivedByEndorse =
    buffers.validInputBlocks
      InputBlocksQuery
        { generatedBetween
        , receivedBy = IbDuringEndorse
        }
  receivedByDeliver1 = buffers.validInputBlocks q
   where
    q =
      InputBlocksQuery
        { generatedBetween
        , receivedBy = IbDuringProposeOrDeliver1
        }
  -- Order of references in EndorseBlock matters for ledger state, so we stick to lists.
  -- Note: maybe order on (slot, subSlot, vrf proof) should be used instead?
  subset xs ys = all (`elem` ys) xs

  endOfPipelineTime p = slotTime slotConfig (snd (pipelineRange cfg p))

  cond :: EndorseBlock -> Bool
  cond eb = assert assumptions $ acd && b && full
   where
    assumptions =
      null eb.endorseBlocksEarlierStage
        && (null eb.endorseBlocksEarlierPipeline || cfg.variant == Full)
        && eb.slot `inRange` fromMaybe (error "impossible") (stageRange cfg voteSendStage slot Endorse)
    -- A. all referenced IBs have been received by the end of the Endorse stage,
    -- C. all referenced IBs validate (wrt. script execution), and,
    -- D. only IBs from this pipeline’s Propose stage are referenced (and not from other pipelines).
    acd = eb.inputBlocks `subset` receivedByEndorse
    -- B. all IBs seen by the end of the Deliver 1 stage are referenced,
    b = receivedByDeliver1 `subset` eb.inputBlocks
    -- assumes eb.endorseBlocksEarlierPipeline are in pipeline order.
    full =
      and $
        zipWith elem eb.endorseBlocksEarlierPipeline $
          [ map (.id) es
          | (_, es) <-
              endorseBlocksToReference
                cfg
                (endorseBlockPipeline cfg eb)
                ebuffers
                ( \p t ->
                    addUTCTime cfg.headerDiffusionTime t < endOfPipelineTime p
                )
          , not (null es)
          ]

endorseBlocksToVoteFor ::
  LeiosConfig ->
  SlotConfig ->
  -- | current slot
  SlotNo ->
  InputBlocksSnapshot ->
  EndorseBlocksSnapshot ->
  [EndorseBlock]
endorseBlocksToVoteFor cfg@LeiosConfig{voteSendStage} slotConfig slot ibs ebs =
  let cond = shouldVoteOnEB cfg slotConfig slot ibs ebs
   in filter cond $
        maybe [] ebs.validEndorseBlocks (stageRange cfg voteSendStage slot Endorse)

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

numWins ::
  StakeFraction ->
  NetworkRate ->
  -- | VRF value
  Double ->
  Word64
numWins (StakeFraction sigma) (NetworkRate rate) p =
  case dropWhile ((p >) . snd) [(v, cumulative dist (fromIntegral v)) | v <- [0 ..]] of
    [] -> error "internal"
    ((v, _) : _) -> v
 where
  dist = poisson (sigma * rate)

-- | Datatype used to mark a sortition closure that should be kept and reused across slots.
--   `data` rather than `newtype` so setup computations can be triggered by matching.
data Sortition = Sortition !(Double -> Word64)

sortition :: StakeFraction -> NetworkRate -> Sortition
sortition stake rate = Sortition (numWins stake rate)

prop_sortition :: StakeFraction -> NetworkRate -> Double -> Bool
prop_sortition x@(StakeFraction stake) y@(NetworkRate rate) = \p ->
  let wins = fromIntegral $ f p
      dist = cumulative (poisson (stake * rate))
   in (p == 0 || dist (wins - 1) < p) && p <= dist wins
 where
  Sortition f = sortition x y
