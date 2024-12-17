{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The \"mempool\" for input blocks.
module RelayProtocol (
  RelayBuffer (..),
  newRelayBuffer,
  modifyRelayBuffer,
  BlockQueue,
  emptyBlockQueue,
  nullBlockQueue,
  snocBlockQueue,
  unconsBlockQueue,
  blockQueueBlocks,
  Ticket,
  BlockWithTicket (..),
  zeroTicket,
  takeAfterTicket,
  lookupByTicket,
  BlockRelayMessage (..),
  relayServer,
  BlockRelayConfig (..),
  BlockTTL (..),
  relayClient,
) where

import Control.Exception (assert)
import Control.Monad (when)
import Data.FingerTree (FingerTree)
import qualified Data.FingerTree as FingerTree
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word (Word64)
import STMCompat
import TimeCompat

import Chan (Chan (readChan, writeChan))
import ChanTCP (MessageSize (..))

-- | The block relay buffer is a queue of blocks. The buffer is used to
-- communicate currently active valid blocks.
--
-- Blocks are expired from the buffer based on a policy.
--
-- This buffer is the source and destination for the protocol that diffuses
-- blocks between peers.
newtype RelayBuffer m blk blkid = RelayBuffer (TVar m (BlockQueue blk blkid))

data BlockQueue blk blkid
  = BlockQueue
      !(FingerTree BlockQueueMeasure (BlockWithTicket blk blkid))
      !(Map blkid Ticket)
      !Ticket -- next one to use
  deriving (Show)

data BlockWithTicket blk blkid = BlockWithTicket !blk !blkid !Ticket
  deriving (Eq, Show)

newtype Ticket = Ticket Word64
  deriving (Eq, Ord, Show, Bounded)

data BlockQueueMeasure = BlockQueueMeasure
  { mMinTicket :: !Ticket
  , mMaxTicket :: !Ticket
  }
  deriving (Show)

instance FingerTree.Measured BlockQueueMeasure (BlockWithTicket blk blkid) where
  measure (BlockWithTicket _ _ pno) = BlockQueueMeasure pno pno

instance Semigroup BlockQueueMeasure where
  vl <> vr =
    BlockQueueMeasure
      (mMinTicket vl `min` mMinTicket vr)
      (mMaxTicket vl `max` mMaxTicket vr)

instance Monoid BlockQueueMeasure where
  mempty = BlockQueueMeasure maxBound minBound
  mappend = (<>)

emptyBlockQueue :: BlockQueue blk blkid
emptyBlockQueue = BlockQueue FingerTree.empty Map.empty tic
 where
  -- Ticket 0 is reserved for `zeroTicket` so takeAfterTicket blkq
  -- zeroTicket always returns all elements.
  tic = Ticket 1

nullBlockQueue :: BlockQueue blk blkid -> Bool
nullBlockQueue (BlockQueue ps _ _) = FingerTree.null ps

snocBlockQueue ::
  Ord blkid =>
  blk ->
  blkid ->
  BlockQueue blk blkid ->
  BlockQueue blk blkid
snocBlockQueue blk blkid (BlockQueue ps idx counter@(Ticket n)) =
  BlockQueue
    (ps FingerTree.|> BlockWithTicket blk blkid counter)
    (Map.insert blkid counter idx)
    (Ticket (n + 1))

unconsBlockQueue ::
  Ord blkid =>
  BlockQueue blk blkid ->
  Maybe (blk, BlockQueue blk blkid)
unconsBlockQueue (BlockQueue ps idx counter) =
  case FingerTree.viewl ps of
    FingerTree.EmptyL -> Nothing
    BlockWithTicket blk blkid _ FingerTree.:< ps' ->
      let blkq' = BlockQueue ps' (Map.delete blkid idx) counter
       in Just (blk, blkq')

lookupByBlockId :: Ord blkid => BlockQueue blk blkid -> blkid -> Maybe blk
lookupByBlockId pq@(BlockQueue _ idx _) blkid =
  Map.lookup blkid idx >>= lookupByTicket pq

lookupByTicket :: BlockQueue blk blkid -> Ticket -> Maybe blk
lookupByTicket (BlockQueue ps _ _) n =
  case FingerTree.search
    ( \ml mr ->
        mMaxTicket ml >= n
          && mMinTicket mr > n
    )
    ps of
    FingerTree.Position _ (BlockWithTicket blk _ n') _ | n' == n -> Just blk
    _ -> Nothing

zeroTicket :: Ticket
zeroTicket = Ticket 0

takeAfterTicket :: BlockQueue blk blkid -> Ticket -> [BlockWithTicket blk blkid]
takeAfterTicket (BlockQueue blkq _ _) n =
  case FingerTree.search
    ( \ml mr ->
        mMaxTicket ml >= n
          && mMinTicket mr > n
    )
    blkq of
    FingerTree.Position _ blk@(BlockWithTicket _ _ n') r
      | n' == n -> Foldable.toList r
      | otherwise -> blk : Foldable.toList r
    FingerTree.OnLeft -> Foldable.toList blkq
    FingerTree.OnRight -> []
    FingerTree.Nowhere -> error "impossible"

fingerprintBlockQueue :: BlockQueue blk blkid -> Ticket
fingerprintBlockQueue (BlockQueue _ _ counter) = counter

blockQueueBlocks :: Ord blkid => BlockQueue blk blkid -> [(blk, blkid)]
blockQueueBlocks (BlockQueue blkq _ _) =
  [(blk, blkid) | BlockWithTicket blk blkid _ <- Foldable.toList blkq]

blockQueueBlockIdsSet :: Ord blkid => BlockQueue blk blkid -> Set blkid
blockQueueBlockIdsSet (BlockQueue _ idx _) = Map.keysSet idx

newRelayBuffer :: MonadSTM m => m (RelayBuffer m blk blkid)
newRelayBuffer = RelayBuffer <$> newTVarIO emptyBlockQueue

modifyRelayBuffer ::
  MonadSTM m =>
  RelayBuffer m blk blkid ->
  (BlockQueue blk blkid -> BlockQueue blk blkid) ->
  STM m ()
modifyRelayBuffer (RelayBuffer buffer) = modifyTVar' buffer

-- | The block relay protocol:
--
-- * Two phase protocol, request block identifiers, then request blocks.
-- * Block ids are smallish 32 byte hashes, but blocks can be large.
-- * A node will request block ids from all peers, but fetch blocks from a
--   single peer: the first one to inform us.
-- * No retry logic is needed for this sim: we assume no failures.
-- * It is possible for blocks to expire between when the block id is
--   notified and the block is requested. This is ok.
-- * The reply with block ids also includes selected block metadata: initially
--   just the TTL of the block. This is used to avoid requesting expired blocks
--   and also to allow policies on the order in which blocks are requested.
data BlockRelayMessage blk blkid blkmd
  = MsgReqBlockIdsBlocking
  | MsgReqBlockIdsNonBlocking
  | MsgRespBlockIds [(blkid, blkmd)]
  | MsgReqBlock blkid
  | MsgRespBlock blk
  | MsgRespNoBlock blkid
  deriving (Show)

instance MessageSize blk => MessageSize (BlockRelayMessage blk blkid blkmd) where
  messageSizeBytes MsgReqBlockIdsBlocking = 10
  messageSizeBytes MsgReqBlockIdsNonBlocking = 10
  messageSizeBytes MsgRespBlockIds{} = 100 -- crude approximation
  messageSizeBytes MsgReqBlock{} = 50
  messageSizeBytes (MsgRespBlock blk) = 10 + messageSizeBytes blk
  messageSizeBytes MsgRespNoBlock{} = 50

newtype BlockTTL = BlockTTL UTCTime
  deriving (Eq, Ord, Show)

data BlockRelayConfig m blk blkid = BlockRelayConfig
  { blockId :: blk -> blkid
  , blockTTL :: blk -> BlockTTL
  , submitBlock :: blk -> STM m () -> m ()
  }

relayServer ::
  forall m blk blkid.
  (MonadSTM m, Ord blkid) =>
  BlockRelayConfig m blk blkid ->
  RelayBuffer m blk blkid ->
  Chan m (BlockRelayMessage blk blkid BlockTTL) ->
  m ()
relayServer BlockRelayConfig{blockTTL} (RelayBuffer buffer) chan =
  go (fingerprintBlockQueue emptyBlockQueue)
 where
  go :: Ticket -> m ()
  go !fingerprint = do
    msg <- readChan chan
    case msg of
      MsgReqBlockIdsBlocking -> do
        blkq <- atomically $ do
          blkq <- readTVar buffer
          when (fingerprintBlockQueue blkq == fingerprint) retry
          return blkq
        writeChan chan $
          MsgRespBlockIds
            [ (blkid, blockTTL blk)
            | (blk, blkid) <- blockQueueBlocks blkq
            ]
        go (fingerprintBlockQueue blkq)
      MsgReqBlockIdsNonBlocking -> do
        blkq <- readTVarIO buffer
        writeChan chan $
          MsgRespBlockIds
            [ (blkid, blockTTL blk)
            | (blk, blkid) <- blockQueueBlocks blkq
            ]
        go (fingerprintBlockQueue blkq)
      MsgReqBlock blkid -> do
        mblk <- atomically $ do
          blkq <- readTVar buffer
          return (lookupByBlockId blkq blkid)
        case mblk of
          Nothing -> do
            writeChan chan (MsgRespNoBlock blkid)
            go fingerprint
          Just blk -> do
            writeChan chan (MsgRespBlock blk)
            go fingerprint
      MsgRespBlockIds{} -> error "relayServer: unexpected message"
      MsgRespBlock{} -> error "relayServer: unexpected message"
      MsgRespNoBlock{} -> error "relayServer: unexpected message"

-- TODO: there is no limit on the size of in-flight set, but there probably
-- should be. It looks like we get osilating behaviour of asking for too much
-- followed by forwarding bursts

relayClient ::
  forall m blk blkid.
  (MonadSTM m, MonadTime m, Ord blkid) =>
  BlockRelayConfig m blk blkid ->
  RelayBuffer m blk blkid ->
  -- | in-flight set shared between all clients
  TVar m (Set blkid) ->
  Chan m (BlockRelayMessage blk blkid BlockTTL) ->
  m ()
relayClient
  BlockRelayConfig{blockId, submitBlock}
  (RelayBuffer buffer)
  inflight
  chan = do
    idle 0
   where
    idle nreplies | nreplies == 0 = do
      writeChan chan MsgReqBlockIdsBlocking
      awaitReply (nreplies + 1)
    idle nreplies =
      awaitReply nreplies

    awaitReply nreplies = assert (nreplies > 0) $ do
      msg <- readChan chan
      case msg of
        MsgRespBlockIds availableBlkIds -> do
          -- Decide immediately if any are new, not-expired, and request them.
          -- They're new if they're not in the buffer, and also not in flight.
          -- They're not expired if their TTL is >= now
          -- If they're new, add them to the in-flight set and request them.
          -- If none are new, go back to asking for more blkids.
          now <- getCurrentTime
          mnewBlkIds <- atomically $ do
            oldBlkIds <-
              Set.union
                <$> readTVar inflight
                <*> (blockQueueBlockIdsSet <$> readTVar buffer)
            let newBlkIds =
                  [ (blkid, ttl)
                  | (blkid, ttl) <- availableBlkIds
                  , blkid `Set.notMember` oldBlkIds
                  , ttl >= BlockTTL now
                  ]
                newBlkIdsSet = Set.fromList (map fst newBlkIds)
            if null newBlkIds
              then return Nothing
              else do
                modifyTVar' inflight (Set.union newBlkIdsSet)
                return (Just newBlkIds)
          case mnewBlkIds of
            Nothing -> idle (nreplies - 1)
            Just newBlkIds -> do
              -- request blocks in the order from oldest to newest
              -- Note: this is a place where alternative polciies might request
              -- newest to oldest, or some hybrid (e.g. "recent" (Delta) before
              -- non-recent, but recent ones still oldest to newest).
              sequence_
                [ do
                  writeChan chan (MsgReqBlock blkid)
                  writeChan chan MsgReqBlockIdsNonBlocking
                | (blkid, _ttl) <- sortBy (compare `on` snd) newBlkIds
                ]
              idle (nreplies - 1 + 2 * length newBlkIds)
        MsgRespBlock blk -> do
          -- Submit the block for validation, and when that completes
          -- asynchronously atomically remove from the inflight and add
          -- to the buffer
          submitBlock blk $ do
            let blkid = blockId blk
            modifyTVar' inflight (Set.delete blkid)
            modifyTVar' buffer (snocBlockQueue blk blkid)
          idle (nreplies - 1)
        MsgRespNoBlock blkno -> do
          atomically $
            modifyTVar' inflight (Set.delete blkno)
          idle (nreplies - 1)
        MsgReqBlockIdsBlocking{} -> error "relayClient: unexpected message"
        MsgReqBlockIdsNonBlocking{} -> error "relayClient: unexpected message"
        MsgReqBlock{} -> error "relayClient: unexpected message"
