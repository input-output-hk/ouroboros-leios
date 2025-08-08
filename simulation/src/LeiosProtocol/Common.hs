{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Common (
  module PraosProtocol.Common,
  module TaskMultiQueue,
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
  NodeId (..),
  SubSlotNo (..),
  Word64,
  NetworkRate (..),
  NodeRate (..),
  StakeFraction (..),
  NumCores (..),
  mkStringId,
)
where

import Chan.TCP
import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad (guard)
import Data.Aeson
import Data.Aeson.Types (Parser, unexpected)
import Data.Coerce
import Data.Hashable
import Data.Map (Map)
import qualified Data.Text as T
import Data.Word (Word64, Word8)
import GHC.Generics
import GHC.Records
import PraosProtocol.Common
import SimTypes
import TaskMultiQueue
import Text.Read (readMaybe)

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

type RankingBlockHeader = BlockHeader
data RankingBlockBody = RankingBlockBody
  { endorseBlocks :: ![(EndorseBlockId, Certificate)]
  -- ^ at most one in short leios.
  , payload :: !Bytes
  -- ^ ranking blocks can also contain transactions directly, which we
  -- do not model directly, but contribute to size.
  , nodeId :: !NodeId
  -- ^ convenience to keep track of origin, does not contribute to size.
  , size :: !Bytes
  }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable)

rankingBlockBodyInvariant :: RankingBlockBody -> Bool
rankingBlockBodyInvariant rbb = rbb.payload <= rbb.size

type RankingBlock = Block RankingBlockBody

type RankingBlockId = HeaderHash RankingBlock

data InputBlockId = InputBlockId
  { node :: !NodeId
  , num :: !Int
  }
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)

instance NFData InputBlockId where
  rnf InputBlockId{} = ()

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
  , slot :: !SlotNo
  -- ^ duplicated here for convenience of vizualization, does not contribute to size.
  }
  deriving stock (Eq, Show)

data InputBlock = InputBlock
  { header :: !InputBlockHeader
  , body :: !InputBlockBody
  }
  deriving stock (Eq, Show)

inputBlockInvariant :: InputBlock -> Bool
inputBlockInvariant ib = ib.header.id == ib.body.id

instance HasField "id" InputBlock InputBlockId where
  getField = (.id) . (.header)

instance HasField "slot" InputBlock SlotNo where
  getField = (.slot) . (.header)

data EndorseBlockId = EndorseBlockId
  { node :: !NodeId
  , num :: !Int
  }
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable)

instance NFData EndorseBlockId where
  rnf EndorseBlockId{} = ()

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
  , votes :: Word64
  , endorseBlocks :: ![EndorseBlockId]
  , size :: !Bytes
  }
  deriving stock (Eq, Show)

newtype Certificate = Certificate
  { votes :: Map VoteId Word64
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

mkStringId :: (HasField "node" a NodeId, HasField "num" a Int) => a -> String
mkStringId x = concat [show (coerce @_ @Int x.node), "-", show x.num]

readStringId :: String -> Maybe (NodeId, Int)
readStringId s = do
  (node_s, '-' : i_s) <- pure $ break (== '-') s
  (,) <$> (NodeId <$> readMaybe node_s) <*> readMaybe i_s

instance HasField "stringId" InputBlockHeader String where
  getField = mkStringId . (.id)

instance HasField "stringId" InputBlock String where
  getField = mkStringId . (.id)

instance HasField "stringId" InputBlockBody String where
  getField = mkStringId . (.id)

instance HasField "stringId" VoteMsg String where
  getField = mkStringId . (.id)

instance HasField "stringId" EndorseBlock String where
  getField = mkStringId . (.id)

instance ToJSON InputBlockId where
  toJSON = toJSON . mkStringId

instance FromJSON InputBlockId where
  parseJSON = parseStringId InputBlockId

instance ToJSON EndorseBlockId where
  toJSON = toJSON . mkStringId
instance FromJSON EndorseBlockId where
  parseJSON = parseStringId EndorseBlockId

instance ToJSON VoteId where
  toJSON = toJSON . mkStringId
instance FromJSON VoteId where
  parseJSON = parseStringId VoteId

parseStringId :: (NodeId -> Int -> a) -> Value -> Parser a
parseStringId c (String s) = maybe (fail "string id not readable") (pure . uncurry c) $ readStringId (T.unpack s)
parseStringId _ v = unexpected v
