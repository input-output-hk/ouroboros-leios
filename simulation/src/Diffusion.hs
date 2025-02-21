{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module Diffusion
where

import Control.Monad
import Data.Aeson
import Data.Bifunctor
import Data.Coerce
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable
import GHC.Generics
import LeiosProtocol.Common hiding (Point)
import qualified PraosProtocol.Common.Chain as Chain

data DiffusionEntry id = DiffusionEntry
  { block_id :: !id
  , node_id :: !Int
  , created :: !DiffTime
  , adoptions :: ![(NodeId, DiffTime)]
  }
  deriving (Generic, ToJSON, FromJSON)

data DiffusionData id = DiffusionData
  { entries :: ![DiffusionEntry id]
  , latency_per_stake :: ![LatencyPerStake id]
  -- ^ adoption latency, counted from slot start.
  , average_latencies :: !(Map.Map Double DiffTime)
  -- ^ map from stake fraction to average adoption latency
  }
  deriving (Generic, ToJSON, FromJSON)

data LatencyPerStake id = LatencyPerStake
  { block_id :: !id
  , latencies :: ![(Maybe DiffTime, Double)]
  }
  deriving (Generic, ToJSON, FromJSON)

diffusionEntryToLatencyPerStake :: Map NodeId StakeFraction -> DiffusionEntry id -> LatencyPerStake id
diffusionEntryToLatencyPerStake stakes DiffusionEntry{..} =
  LatencyPerStake
    { block_id
    , latencies = bin $ coerce $ diffusionLatencyPerStakeFraction stakes slotStart adoptions
    }
 where
  slotStart = fromIntegral @Integer $ floor created
  bins = [0.50, 0.8, 0.9, 0.92, 0.94, 0.96, 0.98, 1]
  bin xs = map (\b -> (,b) $ fst <$> listToMaybe (dropWhile (\(_, x) -> x < b) xs)) bins

diffusionLatencyPerStakeFraction ::
  Map NodeId StakeFraction ->
  DiffTime ->
  [(NodeId, DiffTime)] ->
  LatencyPerStakeCdf
diffusionLatencyPerStakeFraction stakes t0 =
  snd
    . mapAccumL h 0
    . map (first (stakes Map.!))
    . reverse
 where
  h s (StakeFraction ns, t) =
    let
      !s' = s + ns
      !latency = t - t0
     in
      (s', (latency, StakeFraction s'))

-- | In ascending order of StakeFraction
type LatencyPerStakeCdf = [(DiffTime, StakeFraction)]

-- Given a LatencyPerStakeCdf for each block, returns a map from
-- requested stakes to all block latencies to reach that stake.
transposeLatenciesPerStake :: [LatencyPerStakeCdf] -> Set StakeFraction -> Map StakeFraction [DiffTime]
transposeLatenciesPerStake cdfs stakes =
  Map.unionsWith (++)
    . map (Map.fromAscList . map (second (: [])) . sample stakeBins)
    $ cdfs
 where
  stakeBins = Set.toAscList stakes
  sample :: [StakeFraction] -> LatencyPerStakeCdf -> [(StakeFraction, DiffTime)]
  sample [] _ = []
  sample (bin : bins) cdf = case dropWhile ((< bin) . snd) cdf of
    [] -> []
    ((l, _) : _) -> (bin, l) : sample bins cdf

stableChainHashes :: HasHeader a => IntMap (Chain a) -> [HeaderHash a]
stableChainHashes chains =
  let stable_chain = fromMaybe Genesis $ do
        guard $ not $ IMap.null chains
        pure $ List.foldl1' aux (IMap.elems chains)
      aux c1 c2 = fromMaybe Genesis $ do
        p <- Chain.intersectChains c1 c2
        Chain.rollback p c1
   in map blockHash $ Chain.toNewestFirst stable_chain

diffusionEntries :: Map id (msg, NodeId, Time, [(NodeId, Time)]) -> [DiffusionEntry id]
diffusionEntries arrivals =
  [ DiffusionEntry{..}
  | (block_id, (_, NodeId node_id, Time created, ts)) <- Map.toList arrivals
  , let adoptions = map (second (\(Time t) -> t)) ts
  ]

diffusionDataFromEntries ::
  Bool ->
  Map NodeId StakeFraction ->
  [DiffusionEntry id] ->
  DiffusionData id
diffusionDataFromEntries analize stakes entries = DiffusionData{..}
 where
  latency_per_stake
    | analize = map (diffusionEntryToLatencyPerStake stakes) entries
    | otherwise = []
  avg ts = sum ts / fromIntegral (length ts)
  average_latencies
    | analize =
        Map.map avg $
          Map.fromListWith
            (++)
            [ (p, [d])
            | l <- latency_per_stake
            , (Just d, p) <- l.latencies
            ]
    | otherwise = Map.empty
