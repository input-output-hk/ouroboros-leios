{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Spec.Generated where

import Control.Lens hiding (_1, _2, elements)
import Control.Monad ((<=<), mzero)
import Control.Monad.State
import Data.Default (Default(..))
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Word (Word16, Word64)
import Data.Set (Set)
import Data.Text (Text)
import LeiosConfig (CleanupPolicy(..), CleanupPolicies(..), Config(..), DiffusionStrategy(..), Distribution(..), LeiosVariant(..), RelayStrategy(..))
import LeiosEvents
import LeiosTopology (BandwidthBps(..), CpuCoreCount(..), LinkInfo(..), Location(..), LocationKind(..), Node(..), NodeInfo(..), NodeName(..), Topology(..))
import LeiosTypes (Point(..))
import Lib (verifyTrace)
import Test.Hspec
import Test.QuickCheck hiding (scale)
import Test.Hspec.QuickCheck

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T

config :: Config
config = Config {relayStrategy = RequestFromFirst, tcpCongestionControl = True, multiplexMiniProtocols = True, treatBlocksAsFull = False, cleanupPolicies = CleanupPolicies (S.fromList [CleanupExpiredVote]), simulateTransactions = True, leiosStageLengthSlots = 2, leiosStageActiveVotingSlots = 1, leiosVoteSendRecvStages = False, leiosVariant = Short, leiosHeaderDiffusionTimeMs = 1000.0, praosChainQuality = 20.0, txGenerationDistribution = Exp {lambda = 0.85, scale = pure 1000.0}, txSizeBytesDistribution = LogNormal {mu = 6.833, sigma = 1.127}, txValidationCpuTimeMs = 1.5, txMaxSizeBytes = 16384, rbGenerationProbability = 5.0e-2, rbGenerationCpuTimeMs = 1.0, rbHeadValidationCpuTimeMs = 1.0, rbHeadSizeBytes = 1024, rbBodyMaxSizeBytes = 90112, rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant = 50.0, rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte = 5.0e-4, rbBodyLegacyPraosPayloadAvgSizeBytes = 0, ibGenerationProbability = 5.0, ibGenerationCpuTimeMs = 130.0, ibHeadSizeBytes = 304, ibHeadValidationCpuTimeMs = 1.0, ibBodyValidationCpuTimeMsConstant = 50.0, ibBodyValidationCpuTimeMsPerByte = 5.0e-4, ibBodyMaxSizeBytes = 327680, ibBodyAvgSizeBytes = 98304, ibDiffusionStrategy = FreshestFirst, ibDiffusionMaxWindowSize = 100, ibDiffusionMaxHeadersToRequest = 100, ibDiffusionMaxBodiesToRequest = 1, ibShards = 50, ebGenerationProbability = 1.5, ebGenerationCpuTimeMs = 75.0, ebValidationCpuTimeMs = 1.0, ebSizeBytesConstant = 240, ebSizeBytesPerIb = 32, ebDiffusionStrategy = PeerOrder, ebDiffusionMaxWindowSize = 100, ebDiffusionMaxHeadersToRequest = 100, ebDiffusionMaxBodiesToRequest = 1, ebMaxAgeSlots = 100, ebMaxAgeForRelaySlots = 40, voteGenerationProbability = 500.0, voteGenerationCpuTimeMsConstant = 0.164, voteGenerationCpuTimeMsPerIb = 0.0, voteValidationCpuTimeMs = 0.816, voteThreshold = 300, voteBundleSizeBytesConstant = 0, voteBundleSizeBytesPerEb = 105, voteDiffusionStrategy = PeerOrder, voteDiffusionMaxWindowSize = 100, voteDiffusionMaxHeadersToRequest = 100, voteDiffusionMaxBodiesToRequest = 1, certGenerationCpuTimeMsConstant = 90.0, certGenerationCpuTimeMsPerNode = 0.0, certValidationCpuTimeMsConstant = 130.0, certValidationCpuTimeMsPerNode = 0.0, certSizeBytesConstant = 7168, certSizeBytesPerNode = 0}

topology :: Topology 'COORD2D
topology = Topology {nodes = M.fromList [(NodeName "node-0",Node {nodeInfo = NodeInfo {stake = 500, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D {coord2D = Point {_1 = 0.12000040231003672, _2 = 0.1631004621065356}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-1",LinkInfo {latencyMs = 141.01364015418432, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000}),(NodeName "node-2",LinkInfo {latencyMs = 254.6249782835189, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]}),(NodeName "node-1",Node {nodeInfo = NodeInfo {stake = 200, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D {coord2D = Point {_1 = 0.34276660615051174, _2 = 0.2636899791034371}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-2",LinkInfo {latencyMs = 175.32530255486685, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000}),(NodeName "node-3",LinkInfo {latencyMs = 379.1167948193313, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]}),(NodeName "node-2",Node {nodeInfo = NodeInfo {stake = 100, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D {coord2D = Point {_1 = 0.5150493264153491, _2 = 0.27873594531347595}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-3",LinkInfo {latencyMs = 248.31457793649423, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]}),(NodeName "node-3",Node {nodeInfo = NodeInfo {stake = 0, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D {coord2D = Point {_1 = 0.3503537969220088, _2 = 0.13879558055660354}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-0",LinkInfo {latencyMs = 140.19739576271448, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]})]}

idSut :: Integer
idSut = 0

sut :: Text
sut = "node-" <> T.pack (show idSut)

idOther :: Integer
idOther = 1

other :: Text
other = "node-" <> T.pack (show idOther)

verify :: [TraceEvent] -> (Integer, Text)
verify =
  let
    nrNodes = toInteger . M.size $ nodes topology
    nodeNames = unNodeName <$> (M.keys $ nodes topology)
    stakes = toInteger . stake . nodeInfo <$> (M.elems $ nodes topology)
    stakeDistribution = zip nodeNames stakes
    stageLength = toInteger $ leiosStageLengthSlots config
  in
    verifyTrace nrNodes idSut stakeDistribution stageLength

check
  :: Maybe Integer
  -> Maybe Text
  -> [TraceEvent]
  -> Property
check expectedActions expectedMessage events =
  let
    result = verify events
    expectedMessage' = fromMaybe "ok" expectedMessage
  in
    case expectedActions of
      Nothing -> snd result === expectedMessage'
      Just expectedActions' -> result === (expectedActions', expectedMessage')

data TracingContext =
  TracingContext
  {
    _clock :: Time
  , _slotNo :: SlotNo
  , _rbs :: Map Text Text
  , _ibs :: Set Text
  , _ebs :: Set Text
  , _votes :: Set Text
  }
    deriving Show

instance Default TracingContext where
  def = TracingContext 0 0 mempty mempty mempty mempty

clock :: Lens' TracingContext Time
clock = lens _clock $ \ctx x -> ctx {_clock = x}

slotNo:: Lens' TracingContext SlotNo
slotNo= lens _slotNo $ \ctx x -> ctx {_slotNo = x}

rbs :: Lens' TracingContext (Map Text Text)
rbs = lens _rbs $ \ctx x -> ctx {_rbs = x}

ibs :: Lens' TracingContext (Set Text)
ibs = lens _ibs $ \ctx x -> ctx {_ibs = x}

ebs :: Lens' TracingContext (Set Text)
ebs = lens _ebs $ \ctx x -> ctx {_ebs = x}

votes :: Lens' TracingContext (Set Text)
votes = lens _votes $ \ctx x -> ctx {_votes = x}

data Transition =
    NextSlot
  | SkipSlot
  | GenerateRB
  | ReceiveRB
  | GenerateIB
  | SkipIB
  | ReceiveIB
  deriving Show

genId :: Integer -> Word64 -> Set Text -> Gen Text
genId system slot forbidden =
  let
    g = T.pack . ((show system <> "-" <> show slot <> "-") <>) . show <$> (arbitrary :: Gen Word16)
  in
    g `suchThat` (not . (`S.member` forbidden))

genRB :: Integer -> StateT TracingContext Gen (Text, Nullable BlockRef)
genRB i =
  do
    slot <- use slotNo
    rbs' <- M.keysSet <$> use rbs
    block_id <- lift $ genId i slot rbs'
    parent <-
      if S.null rbs'
        then pure "genesis"
        else lift . elements $ S.toList rbs'
    rbs %= M.insert block_id parent
    pure (block_id, Nullable . pure $ BlockRef parent)

genIB :: Integer -> StateT TracingContext Gen Text
genIB i =
  do
    slot <- use slotNo
    ibs' <- use ibs
    ib <- lift $ genId i slot ibs'
    ibs %= S.insert ib
    pure ib

tick :: StateT TracingContext Gen ()
tick = clock %= (+ 0.000001)

transition :: Transition -> StateT TracingContext Gen [Event]
transition NextSlot =
  do
    event <- Slot sut <$> use slotNo
    slotNo %= (+ 1)
    pure [event]
transition SkipSlot =
  do
    slotNo %= (+ 1)
    pure mempty
transition GenerateRB =
  do
    tick
    let producer = sut
        endorsement = Nullable mzero
        endorsements = mzero
    slot <- use slotNo
    (block_id, parent) <- genRB idSut
    size_bytes <- lift arbitrary
    payload_bytes <- lift arbitrary
    pure [RBGenerated{..}]
transition ReceiveRB =
  do
    tick
    let sender = pure other
        recipient = sut
        block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- pure <$> use clock
    (block_id, _) <- genRB idOther
    pure [RBReceived{..}]
transition GenerateIB =
  do
    tick
    slot <- use slotNo
    let producer = sut
        pipeline = slot `div` fromIntegral (leiosStageLengthSlots config)
    id <- genIB idSut
    size_bytes <- lift arbitrary
    payload_bytes <- lift arbitrary
    rb_ref <- lift . fmap pure . elements . M.keys =<< use rbs
    pure [IBGenerated{..}]
transition SkipIB = pure . pure . NoIBGenerated sut =<< use slotNo
transition ReceiveIB =
  do
    tick
    let sender = pure other
        recipient = sut
        block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- pure <$> use clock
    block_id <- genIB idOther
    pure [IBReceived{..}]

transitions :: [Transition] -> Gen [TraceEvent]
transitions =
  (`evalStateT` def)
    . (mapM timestamp =<<)
    . fmap concat
    . mapM transition

timestamp :: Monad m => Event -> StateT TracingContext m TraceEvent
timestamp = (<$> use clock) . flip TraceEvent

generated :: Spec
generated =
  do
    let single = (modifyMaxSuccess (const 1) .) . prop
    describe "Positive cases" $ do
      single "Genesis slot" $
        check mzero mzero
          <$> transitions [NextSlot]
      single "Generate RB" $
        check mzero mzero
          <$> transitions [NextSlot, GenerateRB]
      single "Generate IB" $
        check mzero mzero
          <$> transitions [NextSlot, GenerateIB]
      single "Generate no IB" $
        check mzero mzero
          <$> transitions [NextSlot, SkipIB]
    describe "Negative cases" $ do
      single "No actions" $
        check mzero (pure "Invalid Action: Slot Slot-Action 1")
          <$> transitions [NextSlot, NextSlot]
      single "Start after genesis" $
        check mzero (pure "Invalid Action: Slot Base\8322b-Action 1")
          <$> transitions [SkipSlot, NextSlot]
      single "Generate equivocated IBs" $
        check mzero (pure "Invalid Action: Slot IB-Role-Action 1")
          <$> transitions [NextSlot, GenerateIB, GenerateIB]
