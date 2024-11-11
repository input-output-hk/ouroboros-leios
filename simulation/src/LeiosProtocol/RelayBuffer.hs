{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE StandaloneDeriving #-}

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
  { entries :: !(FingerTree TicketRange (EntryWithTicket key value))
  , index :: !(Map key Ticket)
  , nextTicket :: !Ticket
  }
  deriving (Show)

instance Functor (RelayBuffer key) where
  fmap f rb = RelayBuffer (FingerTree.fmap' (fmap f) rb.entries) rb.index rb.nextTicket

data EntryWithTicket key value = EntryWithTicket
  { key :: !key
  , value :: !value
  , ticket :: !Ticket
  }
  deriving (Eq, Show)

deriving instance Functor (EntryWithTicket key)

newtype Ticket = Ticket {unTicket :: Word64}
  deriving (Eq, Ord, Show, Bounded)

incrTicket :: Ticket -> Ticket
incrTicket = Ticket . (+ 1) . unTicket

data TicketRange = TicketRange
  { mMinTicket :: !Ticket
  , mMaxTicket :: !Ticket
  }
  deriving (Show)

instance FingerTree.Measured TicketRange (EntryWithTicket key value) where
  measure (EntryWithTicket _ _ pno) = TicketRange pno pno

instance Semigroup TicketRange where
  vl <> vr =
    TicketRange
      (mMinTicket vl `min` mMinTicket vr)
      (mMaxTicket vl `max` mMaxTicket vr)

instance Monoid TicketRange where
  mempty = TicketRange maxBound minBound
  mappend = (<>)

empty :: RelayBuffer key value
empty = RelayBuffer FingerTree.empty Map.empty minBound

null :: RelayBuffer key value -> Bool
null = FingerTree.null . (.entries)

snoc ::
  Ord key =>
  key ->
  value ->
  RelayBuffer key value ->
  RelayBuffer key value
snoc k v rb =
  RelayBuffer
    (rb.entries FingerTree.|> EntryWithTicket k v rb.nextTicket)
    (Map.insert k rb.nextTicket rb.index)
    (incrTicket rb.nextTicket)

uncons ::
  Ord key =>
  RelayBuffer key value ->
  Maybe (value, RelayBuffer key value)
uncons rb =
  case FingerTree.viewl rb.entries of
    FingerTree.EmptyL -> Nothing
    entryL FingerTree.:< entriesL ->
      Just (entryL.value, RelayBuffer entriesL (Map.delete entryL.key rb.index) rb.nextTicket)

lookup :: Ord key => RelayBuffer key value -> key -> Maybe value
lookup rb t = Map.lookup t rb.index >>= lookupByTicket rb

lookupByTicket :: RelayBuffer key value -> Ticket -> Maybe value
lookupByTicket rb t =
  case FingerTree.search (ticketSearchMeasure t) rb.entries of
    FingerTree.Position _ pivot _ | pivot.ticket == t -> Just pivot.value
    _ -> Nothing

ticketSearchMeasure :: Ticket -> TicketRange -> TicketRange -> Bool
ticketSearchMeasure n ml mr = mMaxTicket ml >= n && mMinTicket mr > n

toList :: Ord key => RelayBuffer key value -> [EntryWithTicket key value]
toList rb = Foldable.toList rb.entries

keySet :: Ord key => RelayBuffer key value -> Set key
keySet rb = Map.keysSet rb.index

takeAfterTicket :: RelayBuffer key value -> Ticket -> [EntryWithTicket key value]
takeAfterTicket rb t = Foldable.toList $
  case FingerTree.search (ticketSearchMeasure t) rb.entries of
    FingerTree.Position _entriesL pivot entriesR
      | pivot.ticket == t -> entriesR
      | otherwise -> pivot FingerTree.<| entriesR
    FingerTree.OnLeft -> rb.entries
    FingerTree.OnRight -> FingerTree.empty
    FingerTree.Nowhere -> FingerTree.empty
