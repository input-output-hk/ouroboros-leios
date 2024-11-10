{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}

module LeiosProtocol.DataPool where

import Data.FingerTree (FingerTree)
import qualified Data.FingerTree as FingerTree
import qualified Data.Foldable as Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Word (Word64)

--------------------------------
---- Data Pool
--------------------------------

data DataPool header body
  = DataPool
  { poolData :: !(FingerTree DataPoolMeasure (DataWithTicket header body))
  , poolIndex :: !(Map header Ticket)
  , poolNextTicket :: !Ticket -- next one to use
  }
  deriving (Show)

data DataWithTicket header body = DataWithTicket !header !body !Ticket
  deriving (Eq, Show)

newtype Ticket = Ticket {unTicket :: Word64}
  deriving (Eq, Ord, Show, Bounded)

incrTicket :: Ticket -> Ticket
incrTicket = Ticket . (+ 1) . unTicket

data DataPoolMeasure = DataPoolMeasure
  { mMinTicket :: !Ticket
  , mMaxTicket :: !Ticket
  }
  deriving (Show)

instance FingerTree.Measured DataPoolMeasure (DataWithTicket body header) where
  measure (DataWithTicket _ _ pno) = DataPoolMeasure pno pno

instance Semigroup DataPoolMeasure where
  vl <> vr =
    DataPoolMeasure
      (mMinTicket vl `min` mMinTicket vr)
      (mMaxTicket vl `max` mMaxTicket vr)

instance Monoid DataPoolMeasure where
  mempty = DataPoolMeasure maxBound minBound
  mappend = (<>)

empty :: DataPool header body
empty = DataPool FingerTree.empty Map.empty (Ticket 0)

null :: DataPool header body -> Bool
null = FingerTree.null . (.poolData)

snoc ::
  Ord header =>
  header ->
  body ->
  DataPool header body ->
  DataPool header body
snoc header body (DataPool ps idx counter) =
  DataPool
    (ps FingerTree.|> DataWithTicket header body counter)
    (Map.insert header counter idx)
    (incrTicket counter)

uncons ::
  Ord header =>
  DataPool header body ->
  Maybe (body, DataPool header body)
uncons (DataPool ps idx counter) =
  case FingerTree.viewl ps of
    FingerTree.EmptyL -> Nothing
    DataWithTicket header body _ FingerTree.:< ps' ->
      let bodyq' = DataPool ps' (Map.delete header idx) counter
       in Just (body, bodyq')

lookup :: Ord header => DataPool header body -> header -> Maybe body
lookup pq@(DataPool _ idx _) header =
  Map.lookup header idx >>= lookupByTicket pq

lookupByTicket :: DataPool header body -> Ticket -> Maybe body
lookupByTicket (DataPool pool _ _) n =
  case FingerTree.search (ticketSearchMeasure n) pool of
    FingerTree.Position _ (DataWithTicket _ body n') _ | n' == n -> Just body
    _ -> Nothing

ticketSearchMeasure :: Ticket -> DataPoolMeasure -> DataPoolMeasure -> Bool
ticketSearchMeasure n ml mr = mMaxTicket ml >= n && mMinTicket mr > n

toList :: Ord header => DataPool header body -> [(header, body)]
toList (DataPool pool _ _) =
  [(header, body) | DataWithTicket header body _ <- Foldable.toList pool]

headerSet :: Ord header => DataPool header body -> Set header
headerSet (DataPool _ idx _) = Map.keysSet idx
