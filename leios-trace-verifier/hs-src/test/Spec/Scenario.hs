{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Spec.Scenario (
  config,
  topology,
  idSut,
  idOther,
) where

import Control.Monad (mzero)
import Data.Default (Default (..))
import LeiosConfig (CleanupPolicies (..), CleanupPolicy (..), Config (..), DiffusionStrategy (..), Distribution (..), LeiosVariant (..), RelayStrategy (..))
import LeiosTopology (BandwidthBps (..), CpuCoreCount (..), LinkInfo (..), Location (..), LocationKind (..), Node (..), NodeInfo (..), NodeName (..), Topology (..))
import LeiosTypes (Point (..))

import qualified Data.Map.Strict as M
import qualified Data.Set as S

config :: Config
config = def{relayStrategy = RequestFromFirst, tcpCongestionControl = True, multiplexMiniProtocols = True, treatBlocksAsFull = False, cleanupPolicies = CleanupPolicies (S.fromList [CleanupExpiredVote]), simulateTransactions = True, leiosStageLengthSlots = 2, leiosStageActiveVotingSlots = 1, leiosVoteSendRecvStages = False, leiosVariant = Short, leiosLateIbInclusion = False, leiosHeaderDiffusionTimeMs = 1000.0, praosChainQuality = 20.0, txGenerationDistribution = Exp{lambda = 0.85, scale = pure 1000.0}, txSizeBytesDistribution = LogNormal{mu = 6.833, sigma = 1.127}, txValidationCpuTimeMs = 1.5, txMaxSizeBytes = 16384, rbGenerationProbability = 5.0e-2, rbGenerationCpuTimeMs = 1.0, rbHeadValidationCpuTimeMs = 1.0, rbHeadSizeBytes = 1024, rbBodyMaxSizeBytes = 90112, rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant = 50.0, rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte = 5.0e-4, rbBodyLegacyPraosPayloadAvgSizeBytes = 0, ibGenerationProbability = 5.0, ibGenerationCpuTimeMs = 130.0, ibHeadSizeBytes = 304, ibHeadValidationCpuTimeMs = 1.0, ibBodyValidationCpuTimeMsConstant = 50.0, ibBodyValidationCpuTimeMsPerByte = 5.0e-4, ibBodyMaxSizeBytes = 327680, ibBodyAvgSizeBytes = 98304, ibDiffusionStrategy = FreshestFirst, ibDiffusionMaxWindowSize = 100, ibDiffusionMaxHeadersToRequest = 100, ibDiffusionMaxBodiesToRequest = 1, ibShards = 50, ebGenerationProbability = 1.5, ebGenerationCpuTimeMs = 75.0, ebValidationCpuTimeMs = 1.0, ebSizeBytesConstant = 240, ebSizeBytesPerIb = 32, ebDiffusionStrategy = PeerOrder, ebDiffusionMaxWindowSize = 100, ebDiffusionMaxHeadersToRequest = 100, ebDiffusionMaxBodiesToRequest = 1, ebMaxAgeSlots = 100, ebMaxAgeForRelaySlots = 40, voteGenerationProbability = 500.0, voteGenerationCpuTimeMsConstant = 0.164, voteGenerationCpuTimeMsPerIb = 0.0, voteValidationCpuTimeMs = 0.816, voteThreshold = 300, voteBundleSizeBytesConstant = 0, voteBundleSizeBytesPerEb = 105, voteDiffusionStrategy = PeerOrder, voteDiffusionMaxWindowSize = 100, voteDiffusionMaxHeadersToRequest = 100, voteDiffusionMaxBodiesToRequest = 1, certGenerationCpuTimeMsConstant = 90.0, certGenerationCpuTimeMsPerNode = 0.0, certValidationCpuTimeMsConstant = 130.0, certValidationCpuTimeMsPerNode = 0.0, certSizeBytesConstant = 7168, certSizeBytesPerNode = 0}

topology :: Topology 'COORD2D
topology = Topology{nodes = M.fromList [(NodeName "node-0", Node{nodeInfo = NodeInfo{stake = 500, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D{coord2D = Point{_1 = 0.12000040231003672, _2 = 0.1631004621065356}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-1", LinkInfo{latencyMs = 141.01364015418432, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000}), (NodeName "node-2", LinkInfo{latencyMs = 254.6249782835189, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]}), (NodeName "node-1", Node{nodeInfo = NodeInfo{stake = 200, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D{coord2D = Point{_1 = 0.34276660615051174, _2 = 0.2636899791034371}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-2", LinkInfo{latencyMs = 175.32530255486685, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000}), (NodeName "node-3", LinkInfo{latencyMs = 379.1167948193313, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]}), (NodeName "node-2", Node{nodeInfo = NodeInfo{stake = 100, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D{coord2D = Point{_1 = 0.5150493264153491, _2 = 0.27873594531347595}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-3", LinkInfo{latencyMs = 248.31457793649423, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]}), (NodeName "node-3", Node{nodeInfo = NodeInfo{stake = 0, cpuCoreCount = CpuCoreCount mzero, location = LocCoord2D{coord2D = Point{_1 = 0.3503537969220088, _2 = 0.13879558055660354}}, adversarial = mzero}, producers = M.fromList [(NodeName "node-0", LinkInfo{latencyMs = 140.19739576271448, bandwidthBytesPerSecond = BandwidthBps $ pure 1024000})]})]}

idSut :: Integer
idSut = 0

idOther :: Integer
idOther = 1
