{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}

module LeiosProtocol.RelayBuffer where

import Data.FingerTree (FingerTree)
import qualified Data.FingerTree as FingerTree
import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Word (Word64)

--------------------------------
---- Relay Buffer
--------------------------------

data RelayBuffer key value
  = RelayBuffer
  { bufferData :: !(FingerTree RelayBufferMeasure (EntryWithTicket key value))
  , bufferIndex :: !(Map key Ticket)
  , bufferNextTicket :: !Ticket -- next one to use
  }
  deriving (Show)

data EntryWithTicket key value = EntryWithTicket
  { key :: !key
  , value :: !value
  , ticket :: !Ticket
  }
  deriving (Eq, Show)

newtype Ticket = Ticket {unTicket :: Word64}
  deriving (Eq, Ord, Show, Bounded)

incrTicket :: Ticket -> Ticket
incrTicket = Ticket . (+ 1) . unTicket

data RelayBufferMeasure = RelayBufferMeasure
  { mMinTicket :: !Ticket
  , mMaxTicket :: !Ticket
  }
  deriving (Show)

instance FingerTree.Measured RelayBufferMeasure (EntryWithTicket key value) where
  measure (EntryWithTicket _ _ pno) = RelayBufferMeasure pno pno

instance Semigroup RelayBufferMeasure where
  vl <> vr =
    RelayBufferMeasure
      (mMinTicket vl `min` mMinTicket vr)
      (mMaxTicket vl `max` mMaxTicket vr)

instance Monoid RelayBufferMeasure where
  mempty = RelayBufferMeasure maxBound minBound
  mappend = (<>)

empty :: RelayBuffer key value
empty = RelayBuffer FingerTree.empty Map.empty (Ticket 0)

null :: RelayBuffer key value -> Bool
null = FingerTree.null . (.bufferData)

snoc ::
  Ord key =>
  key ->
  value ->
  RelayBuffer key value ->
  RelayBuffer key value
snoc k v (RelayBuffer buffer index counter) =
  RelayBuffer
    (buffer FingerTree.|> EntryWithTicket k v counter)
    (Map.insert k counter index)
    (incrTicket counter)

uncons ::
  Ord key =>
  RelayBuffer key value ->
  Maybe (value, RelayBuffer key value)
uncons (RelayBuffer buffer index counter) =
  case FingerTree.viewl buffer of
    FingerTree.EmptyL -> Nothing
    entry FingerTree.:< entries ->
      let buffer' = RelayBuffer entries (Map.delete entry.key index) counter
       in Just (entry.value, buffer')

lookup :: Ord key => RelayBuffer key value -> key -> Maybe value
lookup pq@(RelayBuffer _ k _) t =
  Map.lookup t k >>= lookupByTicket pq

lookupByTicket :: RelayBuffer key value -> Ticket -> Maybe value
lookupByTicket (RelayBuffer buffer _ _) t =
  case FingerTree.search (ticketSearchMeasure t) buffer of
    FingerTree.Position _ entry _ | entry.ticket == t -> Just entry.value
    _ -> Nothing

ticketSearchMeasure :: Ticket -> RelayBufferMeasure -> RelayBufferMeasure -> Bool
ticketSearchMeasure n ml mr = mMaxTicket ml >= n && mMinTicket mr > n

-- toList :: Ord key => RelayBuffer key value -> [(key, value)]
-- toList (RelayBuffer buffer _ _) =
--   [(entry.key, entry.value) | entry <- Foldable.toList buffer]

keySet :: Ord key => RelayBuffer key value -> Set key
keySet (RelayBuffer _ idx _) = Map.keysSet idx

takeAfterTicket :: RelayBuffer key value -> Ticket -> [EntryWithTicket key value]
takeAfterTicket (RelayBuffer buffer _ _) t =
  case FingerTree.search (ticketSearchMeasure t) buffer of
    FingerTree.Position _ entry r
      | entry.ticket == t -> Foldable.toList r
      | otherwise -> entry : Foldable.toList r
    FingerTree.OnLeft -> Foldable.toList buffer
    FingerTree.OnRight -> []
    FingerTree.Nowhere -> error "impossible"
