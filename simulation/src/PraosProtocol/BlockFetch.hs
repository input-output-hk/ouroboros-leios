{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module PraosProtocol.BlockFetch where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TVar,
    atomically,
    modifyTVar',
    newTVar,
    readTVar,
    retry,
    writeTVar
  ),
 )
import Control.Exception (assert)
import Control.Monad (forM, forever, guard, replicateM, (<=<))
import Data.Bifunctor (second)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (Refl))
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (NonPipelined),
  Protocol (..),
  StateTokenI (..),
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import PraosProtocol.Common
import qualified PraosProtocol.Common.AnchoredFragment as AnchoredFragment
import qualified PraosProtocol.Common.Chain as Chain

data BlockFetchState
  = StIdle
  | StBusy
  | StStreaming
  | StDone
  deriving (Show)

data SingBlockFetchState (st :: BlockFetchState) where
  SingStIdle :: SingBlockFetchState StIdle
  SingStBusy :: SingBlockFetchState StBusy
  SingStStreaming :: SingBlockFetchState StStreaming
  SingStDone :: SingBlockFetchState StDone

decideSingBlockFetchState ::
  SingBlockFetchState st ->
  SingBlockFetchState st' ->
  Maybe (st :~: st')
decideSingBlockFetchState SingStIdle SingStIdle = Just Refl
decideSingBlockFetchState SingStBusy SingStBusy = Just Refl
decideSingBlockFetchState SingStStreaming SingStStreaming = Just Refl
decideSingBlockFetchState SingStDone SingStDone = Just Refl
decideSingBlockFetchState _ _ = Nothing

decideBlockFetchState ::
  forall (st :: BlockFetchState) (st' :: BlockFetchState).
  (StateTokenI st, StateTokenI st') =>
  Maybe (st :~: st')
decideBlockFetchState = decideSingBlockFetchState stateToken stateToken

instance Protocol BlockFetchState where
  data Message BlockFetchState from to where
    MsgRequestRange ::
      Point Block ->
      Point Block ->
      Message BlockFetchState StIdle StBusy
    MsgNoBlocks ::
      Message BlockFetchState StBusy StIdle
    MsgStartBatch ::
      Message BlockFetchState StBusy StStreaming
    MsgBlock ::
      BlockBody ->
      Message BlockFetchState StStreaming StStreaming
    MsgBatchDone ::
      Message BlockFetchState StStreaming StIdle
    MsgClientDone ::
      Message BlockFetchState StIdle StDone
  type StateAgency StIdle = ClientAgency
  type StateAgency StBusy = ServerAgency
  type StateAgency StStreaming = ServerAgency
  type StateAgency StDone = NobodyAgency
  type StateToken = SingBlockFetchState

instance StateTokenI StIdle where stateToken = SingStIdle
instance StateTokenI StBusy where stateToken = SingStBusy
instance StateTokenI StStreaming where stateToken = SingStStreaming
instance StateTokenI StDone where stateToken = SingStDone

deriving instance Show (Message BlockFetchState from to)

instance MessageSize (Message BlockFetchState st st') where
  messageSizeBytes = \case
    MsgRequestRange pt1 pt2 -> messageSizeBytes pt1 + messageSizeBytes pt2
    MsgNoBlocks -> 1
    MsgStartBatch -> 1
    MsgBlock blk -> messageSizeBytes blk
    MsgBatchDone -> 1
    MsgClientDone -> 1

blockFetchMessageLabel :: Message BlockFetchState st st' -> String
blockFetchMessageLabel = \case
  MsgRequestRange _ _ -> "MsgRequestRange"
  MsgNoBlocks -> "MsgNoBlocks"
  MsgStartBatch -> "MsgStartBatch"
  MsgBlock _ -> "MsgBlock"
  MsgBatchDone -> "MsgBatchDone"
  MsgClientDone -> "MsgClientDone"

--------------------------------
--- BlockFetch Server
--------------------------------

newtype BlockFetchProducerState m = BlockFetchProducerState
  { blocksVar :: ReadOnly (TVar m Blocks)
  }

resolveRange ::
  MonadSTM m =>
  BlockFetchProducerState m ->
  Point Block ->
  Point Block ->
  STM m (Maybe [BlockBody])
resolveRange st start end = do
  blocks <- readReadOnlyTVar st.blocksVar
  let resolveRangeAcc :: [BlockBody] -> Point Block -> Maybe [BlockBody]
      resolveRangeAcc acc bpoint | start == bpoint = Just acc
      resolveRangeAcc _acc GenesisPoint = Nothing
      resolveRangeAcc acc bpoint@(BlockPoint pslot phash)
        | pointSlot start > pointSlot bpoint = Nothing
        | otherwise = do
            Block{..} <- Map.lookup phash blocks
            guard $ blockSlot blockHeader == pslot
            resolveRangeAcc (blockBody : acc) =<< blockPrevPoint blocks blockHeader
  return $ reverse <$> resolveRangeAcc [] end

blockFetchProducer ::
  forall m.
  MonadSTM m =>
  BlockFetchProducerState m ->
  TS.Server BlockFetchState NonPipelined StIdle m ()
blockFetchProducer st = idle
 where
  idle :: TS.Server BlockFetchState NonPipelined StIdle m ()
  idle = TS.Await $ \case
    MsgRequestRange start end -> TS.Effect $ atomically $ do
      mblocks <- resolveRange st start end -- Note: we could just look at current chain.
      case mblocks of
        Nothing -> return $ TS.Yield MsgNoBlocks idle
        Just blocks -> return $ TS.Yield MsgStartBatch (streaming blocks)
    MsgClientDone -> TS.Done ()

  streaming :: [BlockBody] -> TS.Server BlockFetchState NonPipelined StStreaming m ()
  streaming [] = TS.Yield MsgBatchDone idle
  streaming (block : blocks) = TS.Yield (MsgBlock block) (streaming blocks)

--------------------------------
--- BlockFetch Client
--------------------------------

newtype BlockRequest
  = BlockRequest {blockRequestFragments :: [AnchoredFragment BlockHeader]}
  deriving (Show)
  deriving newtype (Semigroup) -- TODO: we could merge the fragments.

fragmentRange :: AnchoredFragment BlockHeader -> (Point Block, Point Block)
fragmentRange fr = (castPoint $ AnchoredFragment.lastPoint fr, castPoint $ AnchoredFragment.headPoint fr)

blockRequestPoints :: BlockRequest -> [Point Block]
blockRequestPoints (BlockRequest frs) = concatMap (map headerPoint . AnchoredFragment.toOldestFirst) frs

data BlockFetchConsumerState m = BlockFetchConsumerState
  { blockRequestVar :: TVar m BlockRequest
  , addFetchedBlock :: Block -> m ()
  , removeInFlight :: [Point Block] -> m ()
  }

blockFetchConsumer ::
  forall m.
  MonadSTM m =>
  BlockFetchConsumerState m ->
  TC.Client BlockFetchState NonPipelined StIdle m ()
blockFetchConsumer st = idle
 where
  -- does not support preemption of in-flight requests.
  blockRequest :: STM m (AnchoredFragment BlockHeader)
  blockRequest = do
    BlockRequest rs <- readTVar st.blockRequestVar
    case rs of
      [] -> retry
      (r : rs') -> do
        writeTVar st.blockRequestVar (BlockRequest rs')
        return r

  idle :: TC.Client BlockFetchState NonPipelined StIdle m ()
  idle = TC.Effect $ atomically $ do
    fr <- blockRequest
    let range@(start, end) = fragmentRange fr
    return $ TC.Yield (MsgRequestRange start end) $ busy range fr

  busy :: (Point Block, Point Block) -> AnchoredFragment BlockHeader -> TC.Client BlockFetchState NonPipelined StBusy m ()
  busy range fr = TC.Await $ \case
    MsgNoBlocks -> TC.Effect $ do
      -- TODO: controller might just ask this peer again.
      st.removeInFlight (blockRequestPoints $ BlockRequest [fr])
      return idle
    MsgStartBatch -> streaming range $ AnchoredFragment.toOldestFirst fr

  streaming :: (Point Block, Point Block) -> [BlockHeader] -> TC.Client BlockFetchState NonPipelined StStreaming m ()
  streaming range headers = TC.Await $ \msg ->
    case (msg, headers) of
      (MsgBatchDone, []) -> idle
      (MsgBlock block, header : headers') -> TC.Effect $ do
        ifValidBlockBody
          header
          block
          ( do
              st.addFetchedBlock (Block header block)
              return (streaming range headers')
          )
          (error "blockFetchConsumer: invalid block") -- TODO
      (MsgBatchDone, _ : _) -> TC.Effect $ error "TooFewBlocks" -- TODO?
      (MsgBlock _, []) -> TC.Effect $ error "TooManyBlocks" -- TODO?
  ifValidBlockBody hdr bdy t f = do
    -- TODO: threadDelay
    if headerBodyHash hdr == hashBody bdy
      then t
      else f

--------------------------------------------
---- BlockFetch controller
--------------------------------------------

longestChainSelection ::
  forall block header m.
  ( HasHeader block
  , HasHeader header
  , HeaderHash block ~ HeaderHash header
  , MonadSTM m
  ) =>
  [(PeerId, ReadOnly (TVar m (Chain header)))] ->
  ReadOnly (TVar m (ChainProducerState block)) ->
  (block -> header) ->
  STM m (Maybe (PeerId, AnchoredFragment header))
longestChainSelection candidateChainVars cpsVar getHeader = do
  candidateChains <- mapM (\(pId, v) -> (pId,) <$> readReadOnlyTVar v) candidateChainVars
  cps <- readReadOnlyTVar cpsVar
  let
    chain = fmap getHeader cps.chainState
    aux (mpId, c1) (pId, c2) =
      let c = Chain.selectChain c1 c2
       in if Chain.headPoint c == Chain.headPoint c1
            then (mpId, c1)
            else (Just pId, c2)
    -- using foldl' since @selectChain@ is left biased
    (selectedPeer, chain') = List.foldl' aux (Nothing, chain) candidateChains
  return $ do
    peerId <- selectedPeer
    point <- Chain.intersectChains chain chain'
    let suffix =
          snd . fromMaybe (error "longestChainSelection: intersect not on chain") $
            AnchoredFragment.splitAfterPoint (Chain.toAnchoredFragment chain') point
    pure (peerId, suffix)

-- | Note:
--    * a block is added to RequestVar and InFlightVar at the same time.
--    * the block is removed from blockRequestVar when the consumer starts fetching
--      the corresponding fragment.
--    * the block is removed from blocksInFlightVar when it reaches the
--      "ChainDB" i.e. blockBodiesVar, or the consumer encountered a
--      problem when fetching it. TODO!
data PeerStatus m = PeerStatus
  { blockRequestVar :: TVar m BlockRequest
  , blocksInFlightVar :: TVar m (Set (Point Block))
  , peerChainVar :: ReadOnly (TVar m (Chain BlockHeader))
  }

type PeerId = Int

-- | invariant: blocksVar contains all blocks of cpsVar and targetChainVar
data BlockFetchControllerState m = BlockFetchControllerState
  { blocksVar :: TVar m Blocks
  , targetChainVar :: TVar m (Maybe MissingBlocksChain)
  , peers :: Map PeerId (PeerStatus m)
  , cpsVar :: TVar m (ChainProducerState Block)
  }

addPeer ::
  MonadSTM m =>
  PeerId ->
  ReadOnly (TVar m (Chain BlockHeader)) ->
  BlockFetchControllerState m ->
  m (BlockFetchControllerState m)
addPeer peerId peerChainVar blockFetchControllerState = atomically $ do
  blockRequestVar <- newTVar (BlockRequest [])
  blocksInFlightVar <- newTVar Set.empty
  return $
    blockFetchControllerState
      { peers = Map.insert peerId PeerStatus{..} blockFetchControllerState.peers
      }

newBlockFetchControllerState :: MonadSTM m => m (BlockFetchControllerState m)
newBlockFetchControllerState = atomically $ do
  blocksVar <- newTVar Map.empty
  targetChainVar <- newTVar Nothing
  let peers = Map.empty
  cpsVar <- newTVar $ initChainProducerState Chain.Genesis
  return BlockFetchControllerState{..}

blockFetchController :: forall m. MonadSTM m => BlockFetchControllerState m -> m ()
blockFetchController st@BlockFetchControllerState{..} = forever (atomically makeRequests)
 where
  makeRequests :: STM m ()
  makeRequests = do
    let peerChainVars = (map . second) (.peerChainVar) $ Map.toList peers
    (peerId, fr) <- maybe retry pure =<< longestChainSelection peerChainVars (ReadOnly cpsVar) blockHeader
    e <- initMissingBlocksChain <$> readTVar blocksVar <*> (chainState <$> readTVar cpsVar) <*> pure fr
    updateChains st e
    whenMissing e $ \_missingChain -> do
      -- TODO: filterFetched could be reusing the missingChain suffix.
      req <- filterInFlight <=< filterFetched $ fr
      addRequest peerId req

  filterFetched :: AnchoredFragment BlockHeader -> STM m BlockRequest
  filterFetched fr = do
    blocks <- readTVar blocksVar
    pure $ filterBR ((`Map.notMember` blocks) . blockHash) (BlockRequest [fr])

  filterBR :: (BlockHeader -> Bool) -> BlockRequest -> BlockRequest
  filterBR p = BlockRequest . concatMap (AnchoredFragment.filter p) . (.blockRequestFragments)

  filterInFlight :: BlockRequest -> STM m BlockRequest
  filterInFlight br = do
    in_flights <- forM (Map.elems peers) $ \peer -> do
      readTVar peer.blocksInFlightVar
    pure $ List.foldl' (flip $ \s -> filterBR ((`Set.notMember` s) . headerPoint)) br in_flights

  addRequest :: PeerId -> BlockRequest -> STM m ()
  addRequest _pId (BlockRequest []) = return ()
  addRequest pId br = do
    case Map.lookup pId peers of
      Nothing -> error "addRequest: no such peer"
      Just PeerStatus{..} -> do
        modifyTVar' blocksInFlightVar (`Set.union` Set.fromList (blockRequestPoints br))
        modifyTVar' blockRequestVar (<> br)

------------------------------------------------------
---- MissingBlocksChain
------------------------------------------------------

-- | invariants:
--    1. prefix starts at Genesis, and the tip of the prefix is the anchor of the suffix.
--    2. the suffix has one `Left header` element at the start.
data MissingBlocksChain = MissingBlocksChain
  { prefix :: AnchoredFragment Block
  , suffix :: AnchoredFragment BlockOrHeader
  }

newtype BlockOrHeader = BlockOrHeader {unBlockOrHeader :: Either BlockHeader Block}

type instance HeaderHash BlockOrHeader = HeaderHash BlockHeader

instance StandardHash BlockOrHeader

instance HasHeader BlockOrHeader where
  getHeaderFields (BlockOrHeader x) =
    either
      (castHeaderFields . getHeaderFields)
      (castHeaderFields . getHeaderFields)
      x

data ChainsUpdate
  = FullChain (Chain Block)
  | ImprovedPrefix MissingBlocksChain
  | SamePrefix MissingBlocksChain

fillInBlocks :: Blocks -> MissingBlocksChain -> ChainsUpdate
fillInBlocks blocks MissingBlocksChain{..} =
  case addToChain prefix (AnchoredFragment.mapAnchoredFragment blkLookup suffix) of
    (prefix', Just suffix')
      | AnchoredFragment.headPoint prefix < AnchoredFragment.headPoint prefix' ->
          ImprovedPrefix $ MissingBlocksChain prefix' suffix'
      | otherwise -> SamePrefix $ MissingBlocksChain prefix' suffix'
    (prefix', Nothing) ->
      FullChain $
        fromMaybe (error "fillInBlocks: prefix not from genesis") $
          Chain.fromAnchoredFragment prefix'
 where
  blkLookup :: BlockOrHeader -> BlockOrHeader
  blkLookup x@(BlockOrHeader e) = case e of
    Right _ -> x
    Left hdr -> maybe x (BlockOrHeader . Right) . Map.lookup (blockHash hdr) $ blocks
  addToChain c (AnchoredFragment.Empty _) = (c, Nothing)
  addToChain c af@(x AnchoredFragment.:< af') = case x of
    BlockOrHeader (Right blk) -> addToChain (c AnchoredFragment.:> blk) af'
    BlockOrHeader (Left _) -> (c, Just af)

initMissingBlocksChain ::
  Blocks ->
  Chain Block ->
  AnchoredFragment BlockHeader ->
  ChainsUpdate
initMissingBlocksChain blocks c fr =
  fillInBlocks blocks $
    MissingBlocksChain prefix (AnchoredFragment.mapAnchoredFragment (BlockOrHeader . Left) fr)
 where
  pt :: Point Block
  pt = castPoint $ AnchoredFragment.anchorPoint fr
  prefix = case AnchoredFragment.splitAfterPoint (Chain.toAnchoredFragment c) pt of
    Just (before, _) -> before
    Nothing -> error "initMissingBlocksChain: anchor of fragment not on chain"

whenMissing ::
  Monad m =>
  ChainsUpdate ->
  (MissingBlocksChain -> m ()) ->
  m ()
whenMissing (FullChain _) _ = return ()
whenMissing (ImprovedPrefix m) k = k m
whenMissing (SamePrefix m) k = k m

updateChains ::
  forall m.
  MonadSTM m =>
  BlockFetchControllerState m ->
  ChainsUpdate ->
  STM m ()
updateChains BlockFetchControllerState{..} e =
  case e of
    FullChain fullChain -> do
      writeTVar targetChainVar Nothing
      modifyTVar' cpsVar (switchFork fullChain)
    ImprovedPrefix missingChain -> do
      writeTVar targetChainVar (Just missingChain)
      let improvedChain = fromMaybe (error "prefix not from Genesis") $ Chain.fromAnchoredFragment $ missingChain.prefix
      modifyTVar' cpsVar (switchFork improvedChain)
    SamePrefix missingChain -> do
      writeTVar targetChainVar (Just missingChain)

-----------------------------------------------------------
---- Methods for blockFetchConsumer and blockFetchProducer
-----------------------------------------------------------

removeInFlight :: MonadSTM m => BlockFetchControllerState m -> PeerId -> [Point Block] -> STM m ()
removeInFlight BlockFetchControllerState{..} pId points = do
  let peer = fromMaybe (error "missing peer") $ Map.lookup pId peers
  modifyTVar' peer.blocksInFlightVar (\s -> List.foldl' (flip Set.delete) s points)

-- | Adds validated block to the state.
--   * removes block from PeerId's in-flight set
--   * adds block to blocksVar
--   * @fillInBlocks@ on @selectedChain@, and @updateChains@
addFetchedBlock :: MonadSTM m => BlockFetchControllerState m -> PeerId -> Block -> STM m ()
addFetchedBlock st pId blk = do
  removeInFlight st pId [blockPoint blk]
  modifyTVar' st.blocksVar (Map.insert (blockHash blk) blk)

  selected <- readTVar st.targetChainVar
  case selected of
    Nothing -> return () -- I suppose we do not need this block anymore.
    Just missingChain -> do
      updateChains st =<< fillInBlocks <$> readTVar st.blocksVar <*> pure missingChain

addProducedBlock :: MonadSTM m => BlockFetchControllerState m -> Block -> STM m ()
addProducedBlock BlockFetchControllerState{..} blk = do
  cps <- readTVar cpsVar
  assert (Chain.validExtension cps.chainState blk) $ do
    writeTVar cpsVar $! addBlock blk cps
    modifyTVar' blocksVar (Map.insert (blockHash blk) blk)

    -- We reset the target chain because ours might be longest now:
    -- the controller will wake up and decide, and we do not want to
    -- switch to the target chain before that.
    writeTVar targetChainVar Nothing

blockRequestVarForPeerId :: PeerId -> BlockFetchControllerState m -> TVar m BlockRequest
blockRequestVarForPeerId peerId blockFetchControllerState =
  case Map.lookup peerId blockFetchControllerState.peers of
    Nothing -> error $ "blockRequestVarForPeerId: no peer with id " <> show peerId
    Just peerStatus -> peerStatus.blockRequestVar

initBlockFetchConsumerStateForPeerId :: MonadSTM m => PeerId -> BlockFetchControllerState m -> BlockFetchConsumerState m
initBlockFetchConsumerStateForPeerId peerId blockFetchControllerState =
  BlockFetchConsumerState
    (blockRequestVarForPeerId peerId blockFetchControllerState)
    (atomically . addFetchedBlock blockFetchControllerState peerId)
    (atomically . removeInFlight blockFetchControllerState peerId)
