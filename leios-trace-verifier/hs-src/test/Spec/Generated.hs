{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Spec.Generated where

import LeiosTopology
import LeiosTypes
import Test.Hspec
import Test.QuickCheck

import qualified Data.Map.Strict as M

topology :: Topology 'COORD2D
topology = Topology {nodes = M.fromList [(NodeName "node-0",Node {nodeInfo = NodeInfo {stake = 500, cpuCoreCount = CpuCoreCount Nothing, location = LocCoord2D {coord2D = Point {_1 = 0.12000040231003672, _2 = 0.1631004621065356}}, adversarial = Nothing}, producers = M.fromList [(NodeName "node-1",LinkInfo {latencyMs = 141.01364015418432, bandwidthBytesPerSecond = BandwidthBps $ Just 1024000}),(NodeName "node-2",LinkInfo {latencyMs = 254.6249782835189, bandwidthBytesPerSecond = BandwidthBps $ Just 1024000})]}),(NodeName "node-1",Node {nodeInfo = NodeInfo {stake = 200, cpuCoreCount = CpuCoreCount Nothing, location = LocCoord2D {coord2D = Point {_1 = 0.34276660615051174, _2 = 0.2636899791034371}}, adversarial = Nothing}, producers = M.fromList [(NodeName "node-2",LinkInfo {latencyMs = 175.32530255486685, bandwidthBytesPerSecond = BandwidthBps $ Just 1024000}),(NodeName "node-3",LinkInfo {latencyMs = 379.1167948193313, bandwidthBytesPerSecond = BandwidthBps $ Just 1024000})]}),(NodeName "node-2",Node {nodeInfo = NodeInfo {stake = 100, cpuCoreCount = CpuCoreCount Nothing, location = LocCoord2D {coord2D = Point {_1 = 0.5150493264153491, _2 = 0.27873594531347595}}, adversarial = Nothing}, producers = M.fromList [(NodeName "node-3",LinkInfo {latencyMs = 248.31457793649423, bandwidthBytesPerSecond = BandwidthBps $ Just 1024000})]}),(NodeName "node-3",Node {nodeInfo = NodeInfo {stake = 0, cpuCoreCount = CpuCoreCount Nothing, location = LocCoord2D {coord2D = Point {_1 = 0.3503537969220088, _2 = 0.13879558055660354}}, adversarial = Nothing}, producers = M.fromList [(NodeName "node-0",LinkInfo {latencyMs = 140.19739576271448, bandwidthBytesPerSecond = BandwidthBps $ Just 1024000})]})]}

generated :: Spec
generated = pure ()
