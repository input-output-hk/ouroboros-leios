{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- This module is for examples and tests (not the library) so orphans are ok
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Concrete block
--
-- The network library should not export a concrete block type at all, except
-- that it might need one in its tests (but not exported). Right now this module
-- serves to isolate this in a specific module so we can identify easily where
-- it is used; eventually it should be simplified and then moved to the
-- network layer tests; the more sophiscated block abstraction (abstracted over
-- an Ouroboros protocol) will live in the consensus layer.
module PraosProtocol.Common.ConcreteBlock (
  module Ouroboros.Network.Block,
  Block (..),
  BlockHeader (..),
  BlockBody (..),
  hashHeader,
  BodyHash (..),
  ConcreteHeaderHash (..),
  hashBody,
  IsBody,

  -- * Creating sample chains
  mkChain,
  mkChainSimple,
  mkAnchoredFragment,
  mkAnchoredFragmentSimple,

  -- * Generator utilities
  mkPartialBlock,
  mkPartialBlockHeader,
  fixupBlock,
  fixupBlockHeader,
  fixupBlockAfterBlock,
  fixupChain,
  fixupAnchoredFragmentFrom,
) where

import Codec.CBOR.Decoding (
  decodeBytes,
  decodeInt,
  decodeListLenOf,
  decodeWord64,
 )
import Codec.CBOR.Encoding (encodeBytes, encodeInt, encodeListLen, encodeWord64)
import Codec.Serialise (Serialise (..))
import Data.ByteString (ByteString)
import Data.Function (fix)
import Data.Hashable (Hashable (hash))
import Data.String (IsString)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks)
import Ouroboros.Network.Block
import Ouroboros.Network.Point (withOrigin)
import Ouroboros.Network.Util.ShowProxy (ShowProxy)
import PraosProtocol.Common.AnchoredFragment (Anchor (..), AnchoredFragment)
import PraosProtocol.Common.AnchoredFragment qualified as AnchoredFragment
import PraosProtocol.Common.Chain (Chain)
import PraosProtocol.Common.Chain qualified as Chain

{-------------------------------------------------------------------------------
  Concrete block shape used currently in the network layer

  This should only exist in the network layer /tests/.
-------------------------------------------------------------------------------}

-- | Our highly-simplified version of a block. It retains the separation
-- between a block header and body, which is a detail needed for the protocols.
data Block body = Block
  { blockHeader :: BlockHeader
  , blockBody :: body
  }
  deriving (Show, Eq, Generic)

-- instance ShowProxy (Block body)

newtype BlockBody = BlockBody ByteString
  deriving (Show, Eq, Ord, IsString, Generic)

instance Hashable BlockBody where
  hash (BlockBody body) = hash body

hashBody :: Hashable body => body -> BodyHash
hashBody body = BodyHash (hash body)

-- | A block header. It retains simplified versions of all the essential
-- elements.
data BlockHeader = BlockHeader
  { headerHash :: HeaderHash BlockHeader
  -- ^ The cached 'HeaderHash' of this header.
  , headerPrevHash :: ChainHash BlockHeader
  -- ^ The 'headerHash' of the previous block header
  , headerSlot :: SlotNo
  -- ^ The Ouroboros time slot index of this block
  , headerBlockNo :: BlockNo
  -- ^ The block index from the Genesis
  , headerBodyHash :: BodyHash
  -- ^ The hash of the corresponding block body
  }
  deriving (Show, Eq, Generic)

instance ShowProxy BlockHeader

-- | Compute the 'HeaderHash' of the 'BlockHeader'.
hashHeader :: BlockHeader -> ConcreteHeaderHash
hashHeader (BlockHeader _ b c d e) = HeaderHash (hash (b, c, d, e))

deriving instance Hashable SlotNo
deriving instance Hashable BlockNo

-- | 'Hashable' instance for 'Hash'
--
-- We don't insist that 'Hashable' in 'StandardHash' because 'Hashable' is
-- only used in the network layer /tests/.
--
-- This requires @UndecidableInstances@ because @Hashable (HeaderHash b)@
-- is no smaller than @Hashable (ChainHash b)@.
instance (StandardHash b, Hashable (HeaderHash b)) => Hashable (ChainHash b)

-- use generic instance

-- | The hash of all the information in a 'BlockHeader'.
newtype ConcreteHeaderHash = HeaderHash Int
  deriving (Show, Eq, Ord, Generic, Hashable, NoThunks)

-- | The hash of all the information in a 'BlockBody'.
newtype BodyHash = BodyHash Int
  deriving (Show, Eq, Ord, Generic, Hashable)

{-------------------------------------------------------------------------------
  HasHeader instances
-------------------------------------------------------------------------------}

instance StandardHash BlockHeader
instance StandardHash (Block body)

type instance HeaderHash BlockHeader = ConcreteHeaderHash
type instance HeaderHash (Block body) = ConcreteHeaderHash

instance HasHeader BlockHeader where
  getHeaderFields hdr =
    HeaderFields
      { headerFieldHash = headerHash hdr
      , headerFieldSlot = headerSlot hdr
      , headerFieldBlockNo = headerBlockNo hdr
      }

instance HasFullHeader BlockHeader where
  blockPrevHash = headerPrevHash

  -- \| The header invariant is that the cached header hash is correct.
  blockInvariant b =
    hashHeader b == headerHash b

instance Typeable body => HasHeader (Block body) where
  getHeaderFields = castHeaderFields . getHeaderFields . blockHeader

instance (Typeable body, Hashable body) => HasFullHeader (Block body) where
  blockPrevHash = castHash . headerPrevHash . blockHeader

  -- \| The block invariant is just that the actual block body hash matches the
  -- body hash listed in the header.
  blockInvariant Block{blockBody, blockHeader} =
    blockInvariant blockHeader
      && headerBodyHash blockHeader == hashBody blockBody

{-------------------------------------------------------------------------------
  Constructing sample chains
-------------------------------------------------------------------------------}

type IsBody body = (Typeable body, Hashable body)

-- | This takes the blocks in order from /oldest to newest/.
mkChain :: IsBody body => [(SlotNo, body)] -> Chain (Block body)
mkChain =
  fixupChain fixupBlock
    . map (uncurry mkPartialBlock)
    . reverse

mkChainSimple :: IsBody body => [body] -> Chain (Block body)
mkChainSimple = mkChain . zip [1 ..]

mkAnchoredFragment ::
  IsBody body =>
  Anchor (Block body) ->
  [(SlotNo, body)] ->
  AnchoredFragment (Block body)
mkAnchoredFragment anchor =
  fixupAnchoredFragmentFrom anchor fixupBlock
    . map (uncurry mkPartialBlock)
    . reverse

mkAnchoredFragmentSimple :: IsBody body => [body] -> AnchoredFragment (Block body)
mkAnchoredFragmentSimple =
  mkAnchoredFragment AnchorGenesis . zip [1 ..]

mkPartialBlock :: Hashable body => SlotNo -> body -> Block body
mkPartialBlock sl body =
  Block
    { blockHeader = mkPartialBlockHeader sl body
    , blockBody = body
    }

mkPartialBlockHeader :: Hashable body => SlotNo -> body -> BlockHeader
mkPartialBlockHeader sl body =
  BlockHeader
    { headerSlot = sl
    , headerHash = partialField "headerHash"
    , headerPrevHash = partialField "headerPrevHash"
    , headerBlockNo = partialField "headerBlockNo"
    , headerBodyHash = hashBody body
    }
 where
  partialField n = error ("mkPartialBlockHeader: you didn't fill in field " ++ n)

{-------------------------------------------------------------------------------
  "Fixup" is used for chain construction in the network tests. These functions
  don't make much sense for real chains.
-------------------------------------------------------------------------------}

-- | Fix up a block so that it fits on top of the given anchor. Only the block
-- number, the previous hash and the block hash are updated; the slot number and
-- the signers are kept intact.
fixupBlock ::
  forall body block.
  Hashable body =>
  HeaderHash block ~ HeaderHash BlockHeader =>
  Anchor block ->
  Block body ->
  Block body
fixupBlock prev b@Block{blockBody, blockHeader} =
  b
    { blockHeader =
        (fixupBlockHeader prev blockHeader)
          { headerBodyHash = hashBody blockBody
          }
    }

-- | Fixup block header to fit it on top of a chain.  Only block number and
-- previous hash are updated; the slot and signer are kept unchanged.
fixupBlockHeader ::
  HeaderHash block ~ HeaderHash BlockHeader =>
  Anchor block ->
  BlockHeader ->
  BlockHeader
fixupBlockHeader prev b =
  fix $ \b' ->
    b
      { headerHash = hashHeader b'
      , headerPrevHash = castHash (AnchoredFragment.anchorToHash prev)
      , headerBlockNo = withOrigin (BlockNo 0) succ (AnchoredFragment.anchorToBlockNo prev)
      }

-- | Fixup a block so to fit it on top of a given previous block.

-- Like 'fixupBlock' but it takes the info from a given block.
--
fixupBlockAfterBlock :: IsBody body => Block body -> Block body -> Block body
fixupBlockAfterBlock prev = fixupBlock (AnchoredFragment.anchorFromBlock prev)

fixupBlocks ::
  HasFullHeader b =>
  (c -> b -> c) ->
  c ->
  -- | Override prev hash and block number based on the anchor
  Anchor b ->
  (Anchor b -> b -> b) ->
  [b] ->
  c
fixupBlocks _f z _ _fixup [] = z
fixupBlocks f z anchor fixup (b0 : c0) =
  fst (go b0 c0)
 where
  go b [] = (z `f` b', b')
   where
    b' = fixup anchor b
  go b (b1 : c1) = (c' `f` b', b')
   where
    (c', b1') = go b1 c1
    b' = fixup (AnchoredFragment.anchorFromBlock b1') b

-- | Fix up the block number and hashes of a 'Chain'. This also fixes up the
-- first block to chain-on from genesis, since by construction the 'Chain' type
-- starts from genesis.
fixupChain ::
  HasFullHeader b =>
  (Anchor b -> b -> b) ->
  [b] ->
  Chain b
fixupChain =
  fixupBlocks
    (Chain.:>)
    Chain.Genesis
    AnchorGenesis

fixupAnchoredFragmentFrom ::
  HasFullHeader b =>
  Anchor b ->
  (Anchor b -> b -> b) ->
  [b] ->
  AnchoredFragment b
fixupAnchoredFragmentFrom anchor =
  fixupBlocks
    (AnchoredFragment.:>)
    (AnchoredFragment.Empty anchor)
    anchor

{-------------------------------------------------------------------------------
  Serialisation
-------------------------------------------------------------------------------}

instance Serialise ConcreteHeaderHash where
  encode (HeaderHash h) = encodeInt h
  decode = HeaderHash <$> decodeInt

instance Serialise BodyHash where
  encode (BodyHash h) = encodeInt h
  decode = BodyHash <$> decodeInt

instance Serialise body => Serialise (Block body) where
  encode Block{blockHeader, blockBody} =
    encodeListLen 2
      <> encode blockHeader
      <> encode blockBody

  decode = do
    decodeListLenOf 2
    Block <$> decode <*> decode

instance Serialise BlockHeader where
  encode
    BlockHeader
      { headerHash = headerHash
      , headerPrevHash = headerPrevHash
      , headerSlot = SlotNo headerSlot
      , headerBlockNo = BlockNo headerBlockNo
      , headerBodyHash = BodyHash headerBodyHash
      } =
      encodeListLen 5
        <> encode headerHash
        <> encode headerPrevHash
        <> encodeWord64 headerSlot
        <> encodeWord64 headerBlockNo
        <> encodeInt headerBodyHash

  decode = do
    decodeListLenOf 5
    BlockHeader
      <$> decode
      <*> decode
      <*> (SlotNo <$> decodeWord64)
      <*> (BlockNo <$> decodeWord64)
      <*> (BodyHash <$> decodeInt)

instance Serialise BlockBody where
  encode (BlockBody b) = encodeBytes b

  decode = BlockBody <$> decodeBytes
