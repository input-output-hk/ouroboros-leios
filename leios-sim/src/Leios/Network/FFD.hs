{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Leios.Network.FFD where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Conc (Signal)
import GHC.Natural (Natural, naturalFromInteger)
import Leios.Node.Types (NodeId)
import Leios.Types (SlotNumber)

type Time = Natural

data NetworkParameters = NetworkParameters
  { deltaHdr :: Natural
  , diameter :: Natural
  , capacity :: Natural -- capacity of links
  , singleHopTime :: Natural
  }

-- \|b|/C

data Network = Network
  { headers :: Map MessageId [(Header, Time, Set NodeId)]
  , bodies :: Map MessageId [(Header, Body, Time, Set NodeId)]
  , prefHdr :: Map (NodeId, MessageId) Header
  , currentTime :: Time
  , sutOutput :: [NetworkRequestMsg]
  , params :: NetworkParameters
  }

data Hash = Hash
  deriving (Eq, Show, Ord)

data VrfLotteryProof = VrfLotteryProof

data Signature = Signature

data Header = Header
  { slotNumber :: SlotNumber
  , creator :: NodeId
  , -- , vrfLotteryProof :: VrfLotteryProof
    hash :: Hash
    -- , signature       :: Signature
  }
  deriving (Eq, Show, Ord)

data Body = Body
  deriving (Eq, Ord)

newtype MessageId = MessageId (SlotNumber, NodeId)
  deriving newtype (Ord, Eq, Show)

data NetworkRequestMsg
  = DiffFB Header Body NodeId
  | DiffHdr Header NodeId
  | FetchHdrs NodeId
  | FetchBdys NodeId

data NetworkResponseMsg
  = DeliverHdrs (Set Header)
  | DeliverBdys (Set (Header, Body))

newtype NetworkError = NetworkError String

stepNetwork :: Network -> Adversary -> NetworkRequestMsg -> Either NetworkError (Maybe NetworkResponseMsg, Network)
stepNetwork nw@Network{currentTime, headers, params, bodies} Adversary{mkHdrs, mkBdys} = \case
  DiffFB hdr bdy nid
    | not (match hdr bdy) -> Left $ NetworkError "Header doesn't match body"
    | hasHdr nw nid (getMessageId hdr) -> Left $ NetworkError "Node already has header"
    | otherwise ->
        let
          networkWithHeader = hdrsAdd nw hdr currentTime nid
          networkWithBody = bdysAdd networkWithHeader hdr bdy currentTime nid
          networkWithPrefHdr = networkWithBody{prefHdr = Map.insert (nid, getMessageId hdr) hdr (prefHdr networkWithBody)}
         in
          Right (Nothing, networkWithPrefHdr)
  DiffHdr hdr nid
    | hasPoE nw nid (getMessageId hdr) -> Left $ NetworkError "Found proof of equivocation"
    | otherwise ->
        let
          networkWithHeader = hdrsAdd nw hdr currentTime nid
          networkWithPrefHdr = networkWithHeader{prefHdr = Map.insertWith (\_ oldVal -> oldVal) (nid, getMessageId hdr) hdr (prefHdr networkWithHeader)}
          f newVal oldVal = oldVal
         in
          Right (Nothing, networkWithPrefHdr)
  FetchHdrs nid ->
    let
      honestHdrs =
        Set.fromList
          [ h | hdrs <- Map.elems headers, (h, t, nids) <- hdrs, nid `notElem` nids, currentTime >= t + deltaHdr params, not $ hasPoE nw nid (getMessageId h)
          ]
      adversarialHdrs = Set.filter (hasPoE nw nid . getMessageId) $ mkHdrs honestHdrs
     in
      -- TODO:
      -- addHeaders and set preferred header if empty(not in paper, check with research)
      Right (Just $ DeliverHdrs $ Set.union honestHdrs adversarialHdrs, nw)
  FetchBdys nid ->
    let
      honestBodies =
        Set.fromList
          [ (h, b) | bdys <- Map.elems bodies, (h, b, t, nids) <- bdys, nid `notElem` nids, prefersHeader nid h, all (== h) $ Map.filterWithKey (\(_, mid') _ -> mid' == getMessageId h) (prefHdr nw), let k = naturalFromInteger $ toInteger $ newerBdys nw h
                                                                                                                                                                                                        in currentTime >= t + (k + diameter params) * singleHopTime params
          ]
      adversarialBodies =
        Set.filter
          ( \(h, b) ->
              match h b
                && not (hasBdy nw nid (getMessageId h))
                && prefersHeader nid h
          )
          $ mkBdys honestBodies
      allBodies = Set.union honestBodies adversarialBodies
      prefersHeader nid' h' = (Just h' ==) $ Map.lookup (nid', getMessageId h') (prefHdr nw)
      updatedNetwork = Set.foldl (\nw' (h', b') -> bdysAdd nw' h' b' currentTime nid) nw allBodies
     in
      Right (Just $ DeliverBdys allBodies, updatedNetwork)

data Adversary = Adversary
  { mkHdrs :: Set Header -> Set Header
  , mkBdys :: Set (Header, Body) -> Set (Header, Body)
  }

--- auxilliary functions

getMessageId :: Header -> MessageId
getMessageId Header{slotNumber, creator} =
  MessageId (slotNumber, creator)

match :: Header -> Body -> Bool
match Header{hash} _ = True

hasHdr :: Network -> NodeId -> MessageId -> Bool
hasHdr Network{headers} nid mid =
  maybe False (any $ \(_, _, nids) -> nid `elem` nids) $ Map.lookup mid headers

hasPoE :: Network -> NodeId -> MessageId -> Bool
hasPoE Network{headers} nid mid =
  maybe False ((> 1) . length) $ Map.lookup mid headers

hasBdy :: Network -> NodeId -> MessageId -> Bool
hasBdy Network{bodies} nid mid =
  maybe False (any $ \(_, _, _, nids) -> nid `elem` nids) $ Map.lookup mid bodies

hdrsAdd :: Network -> Header -> Time -> NodeId -> Network
hdrsAdd nw@Network{headers} hdr@Header{slotNumber, creator} t nid =
  nw
    { headers = Map.alter f mid headers
    }
 where
  mid = MessageId (slotNumber, creator)
  f Nothing = Just [(hdr, t, Set.singleton nid)]
  f (Just hdrs) = Just $ go hdrs
   where
    go [] = [(hdr, t, Set.singleton nid)]
    go ((h, t', nids) : xs) =
      if h == hdr
        then (h, t', Set.insert nid nids) : xs
        else (h, t', nids) : go xs

bdysAdd :: Network -> Header -> Body -> Time -> NodeId -> Network
bdysAdd nw@Network{headers, bodies} hdr@Header{slotNumber, creator} b t nid =
  nw
    { bodies = Map.alter f mid bodies
    }
 where
  mid = MessageId (slotNumber, creator)
  f Nothing = Just [(hdr, b, t, Set.singleton nid)]
  f (Just hdrs) = Just $ go hdrs
   where
    go [] = [(hdr, b, t, Set.singleton nid)]
    go ((h, b, t', nids) : xs) =
      if h == hdr
        then (h, b, t', Set.insert nid nids) : xs
        else (h, b, t', nids) : go xs

newerBdys :: Network -> Header -> Int
newerBdys Network{bodies} h =
  Map.size $ snd $ Map.split (getMessageId h) bodies
