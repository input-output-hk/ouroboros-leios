{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Common (
  module PraosProtocol.Common,
  module Block,
  module TimeCompat,
  RankingBlockHeader,
  RankingBlockBody (..),
  RankingBlock,
  RankingBlockId,
  InputBlockId (..),
  InputBlockHeader (..),
  InputBlockBody (..),
  InputBlock (..),
  inputBlockInvariant,
  EndorseBlockId (..),
  EndorseBlock (..),
  VoteId (..),
  VoteMsg (..),
  Certificate (..),
  slice,
  rankingBlockBodyInvariant,
  NodeId,
  SubSlotNo (..),
)
where

import ChanTCP
import Control.Exception (assert)
import Control.Monad (guard)
import Data.Hashable
import Data.Set (Set)
import Data.Word (Word8)
import GHC.Generics
import Ouroboros.Network.Block as Block
import PraosProtocol.Common (
  ChainHash (..),
  MessageSize (..),
  PraosConfig (..),
  ReadOnly,
  SlotConfig (..),
  TakeOnly,
  asReadOnly,
  asTakeOnly,
  kilobytes,
  readReadOnlyTVar,
  readReadOnlyTVarIO,
  slotConfigFromNow,
  slotTime,
  takeTakeOnlyTMVar,
  tryTakeTakeOnlyTMVar,
 )
import qualified PraosProtocol.Common as Praos
import SimTypes
import TimeCompat

{-
  Note [size of blocks/messages]: we add a `size` field to most
  entities to more easily allow size to be a runtime parameter.

  Note [id fields]: we use uniquely generated `id` fields to identify
  blocks instead of hashes (except for RankingBlock). They are also
  used to verify the header belongs with the body, and anywhere a
  reference to a block is needed. Represented as pairs `(NodeId,Int)`
  to allow independent block generation from each node, but should be
  considered opaque otherwise.

  Note [subSlot, producer, endorseBlocksEarlierStage, endorseBlocksEarlierPipeline]:
  these fields are needed to counter equivocation (subSlot, producer)
  or other versions of Leios, we could remove them for now if they get
  in the way, although it seems eventually we want to simulate all the
  variants.

-}

type RankingBlockHeader = Praos.BlockHeader
data RankingBlockBody = RankingBlockBody
  { endorseBlocks :: ![(EndorseBlockId, Certificate)]
  -- ^ at most one in short leios.
  , payload :: !Bytes
  -- ^ ranking blocks can also contain transactions directly, which we
  -- do not model directly, but contribute to size.
  , size :: !Bytes
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable)

rankingBlockBodyInvariant :: RankingBlockBody -> Bool
rankingBlockBodyInvariant rbb = rbb.payload <= rbb.size

type RankingBlock = Praos.Block RankingBlockBody

type RankingBlockId = HeaderHash RankingBlock

data InputBlockId = InputBlockId
  { node :: !NodeId
  , num :: !Int
  }
  deriving stock (Eq, Ord, Show)

newtype SubSlotNo = SubSlotNo Word8
  deriving stock (Show)
  deriving newtype (Eq, Ord, Num, Enum, Bounded)

data InputBlockHeader = InputBlockHeader
  { id :: !InputBlockId
  , slot :: !SlotNo
  , subSlot :: !SubSlotNo
  -- ^ for generation frequencies higher than 1 per slot.
  , producer :: !NodeId
  , rankingBlock :: !(ChainHash RankingBlock)
  -- ^ points to ledger state for validation.
  , size :: !Bytes
  }
  deriving stock (Eq, Show)

-- TODO: at time of writing IB are described to contain an advice field
-- Quote: `advice: advice describing which transaction scripts validated (phase 2 validation)`
-- Not represented or taken in consideration here.
data InputBlockBody = InputBlockBody
  { id :: !InputBlockId
  , size :: !Bytes
  -- ^ transactions not modeled, only their total size.
  }
  deriving stock (Eq, Show)

data InputBlock = InputBlock
  { header :: !InputBlockHeader
  , body :: !InputBlockBody
  }
  deriving stock (Eq, Show)

inputBlockInvariant :: InputBlock -> Bool
inputBlockInvariant ib = ib.header.id == ib.body.id

data EndorseBlockId = EndorseBlockId
  { node :: !NodeId
  , num :: !Int
  }
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)

data EndorseBlock = EndorseBlock
  { id :: !EndorseBlockId
  , slot :: !SlotNo
  , producer :: !NodeId
  , inputBlocks :: ![InputBlockId]
  , endorseBlocksEarlierStage :: ![EndorseBlockId]
  -- ^ not used in "Short" leios.
  , endorseBlocksEarlierPipeline :: ![EndorseBlockId]
  -- ^ only used in "Full" leios.
  , size :: !Bytes
  }
  deriving stock (Eq, Show)

data VoteId = VoteId
  { node :: !NodeId
  , num :: !Int
  }
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)

data VoteMsg = VoteMsg
  { id :: !VoteId
  , slot :: !SlotNo
  , producer :: !NodeId
  , endorseBlock :: !EndorseBlockId
  , size :: !Bytes
  }
  deriving stock (Eq, Show)

data Certificate = Certificate
  { votes :: Set VoteId
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (Hashable)

-------------------------------------------
---- Common defs
-------------------------------------------

slice :: Int -> SlotNo -> Int -> Maybe (SlotNo, SlotNo)
slice l s x = do
  guard (s' >= 0)
  return (a, b)
 where
  -- taken from formal spec
  s' = (fromEnum s `div` l - x) * l
  a = assert (s' >= 0) $ toEnum s'
  b = assert (s' + l - 1 >= 0) $ toEnum $ s' + l - 1

-------------------------------------------
---- MessageSize instances
-------------------------------------------

instance MessageSize SubSlotNo where
  messageSizeBytes _ = 1

instance MessageSize RankingBlockBody where
  messageSizeBytes b = b.size

instance MessageSize InputBlockId where
  messageSizeBytes _ = 32 {- hash -}

instance MessageSize InputBlockHeader where
  messageSizeBytes b = b.size

instance MessageSize InputBlockBody where
  messageSizeBytes b = b.size

instance MessageSize InputBlock where
  messageSizeBytes b = messageSizeBytes b.header + messageSizeBytes b.body

instance MessageSize EndorseBlockId where
  messageSizeBytes _ = 32 {- hash -}

instance MessageSize EndorseBlock where
  messageSizeBytes b = b.size

instance MessageSize VoteId where
  messageSizeBytes _ = 32 {- hash -}

instance MessageSize VoteMsg where
  messageSizeBytes b = b.size
