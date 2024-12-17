module PraosProtocol.Common.Chain (
  module Ouroboros.Network.Mock.Chain,
  dropUntil,
) where

import Ouroboros.Network.Mock.Chain (
  Chain (..),
  ChainUpdate (..),
  HasHeader (..),
  HeaderHash,
  Point (..),
  addBlock,
  applyChainUpdate,
  applyChainUpdates,
  blockPoint,
  chainToList,
  drop,
  findBlock,
  findFirstPoint,
  foldChain,
  fromAnchoredFragment,
  fromNewestFirst,
  fromOldestFirst,
  genesis,
  head,
  headAnchor,
  headBlockNo,
  headHash,
  headPoint,
  headSlot,
  headTip,
  intersectChains,
  isPrefixOf,
  length,
  null,
  pointIsAfter,
  pointOnChain,
  prettyPrintChain,
  rollback,
  selectBlockRange,
  selectChain,
  selectPoints,
  successorBlock,
  takeWhile,
  toAnchoredFragment,
  toNewestFirst,
  toOldestFirst,
  valid,
  validExtension,
 )

-- | Returns prefix where the head block satisfies the predicate.
dropUntil :: (blk -> Bool) -> Chain blk -> Chain blk
dropUntil _ Genesis = Genesis
dropUntil p c0@(c :> blk)
  | p blk = c0
  | otherwise = dropUntil p c
