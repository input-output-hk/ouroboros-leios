{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
module Network.FFD where
import           Data.Map    (Map)
import qualified Data.Map    as Map
import           Data.Set    (Set)
import qualified Data.Set    as Set
import           Data.Time   (UTCTime)
import           GHC.Conc    (Signal)
import           GHC.Natural (Natural)
import           Node.Types  (NodeId)
import           Types       (SlotNumber)

data NetworkParameters = NetworkParameters {
  deltaHdr   :: Natural
  , diameter :: Natural
  , capacity :: Natural -- capacity of links
}

data Network = Network {
  headers     :: Map MessageId [(Header, UTCTime, Set NodeId)]
  , bodies    :: Map MessageId [(Header, Body, UTCTime, Set NodeId)]
  , sutOutput :: [NetworkRequestMsg]
}

data Hash = Hash

data VrfLotteryProof = VrfLotteryProof

data Signature = Signature

data Header = Header {
  slotNumber :: SlotNumber
  , creator  :: NodeId
  -- , vrfLotteryProof :: VrfLotteryProof
  -- , hash            :: Hash
  -- , signature       :: Signature
} deriving (Eq, Show)

data Body = Body

newtype MessageId = MessageId (SlotNumber, NodeId)
  deriving newtype (Ord, Eq, Show)

data NetworkRequestMsg =
  DiffFB Header Body NodeId
  | DiffHdr Header NodeId
  | FetchHdrs
  | FetchBdys

data NetworkResponseMsg =
  DeliverHdrs [Header]
  | DeliverBdys [Body]

--- auxilliary functions

-- match :: Header -> Body -> Bool
-- match Header {hash} _ = True

hasHdr :: Network -> NodeId -> MessageId -> Bool
hasHdr Network {headers} nid mid =
  maybe False (any $ \(_,_,nids) -> nid `elem` nids) $  Map.lookup mid  headers

hasPoE :: Network -> NodeId -> MessageId -> Bool
hasPoE Network {headers} nid mid =
  maybe False ((> 1) . length) $ Map.lookup mid headers

hasBdy :: Network -> NodeId -> MessageId -> Bool
hasBdy Network {bodies} nid mid =
  maybe False (any $ \(_,_,_,nids) -> nid `elem` nids) $  Map.lookup mid  bodies

hdrsAdd :: Network -> Header -> UTCTime -> NodeId -> Network
hdrsAdd nw@Network {headers} hdr@Header {slotNumber, creator} t nid = nw {
  headers = Map.alter f mid headers
}
  where
    mid = MessageId (slotNumber, creator)
    f Nothing     = Just [(hdr,t,Set.singleton nid)]
    f (Just hdrs) = Just $ go hdrs
      where
        go [] = [(hdr,t,Set.singleton nid)]
        go ((h,t',nids):xs) = if h == hdr
          then (h,t', Set.insert nid nids):xs
          else (h,t',nids): go xs


bdysAdd :: Network -> Header -> Body -> UTCTime -> NodeId -> Network
bdysAdd nw@Network {headers, bodies} hdr@Header {slotNumber, creator} b t nid = nw {
  bodies = Map.alter f mid bodies
}
  where
    mid = MessageId (slotNumber, creator)
    f Nothing     = Just [(hdr,b,t,Set.singleton nid)]
    f (Just hdrs) = Just $ go hdrs
      where
        go [] = [(hdr,b,t,Set.singleton nid)]
        go ((h,b,t',nids):xs) = if h == hdr
          then (h,b,t', Set.insert nid nids):xs
          else (h,b,t',nids): go xs

newerBdys :: Network -> Header -> Int
newerBdys = undefined


