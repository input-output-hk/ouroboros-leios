{-# LANGUAGE BangPatterns #-}
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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

module PraosProtocol.BlockFetch where

import Chan (Chan)
import ChanDriver (ProtocolMessage, chanDriver)
import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TVar,
    atomically,
    modifyTVar',
    newTVar,
    newTVarIO,
    readTVar,
    readTVarIO,
    retry,
    writeTVar
  ),
 )
import Control.Concurrent.Class.MonadSTM.TBQueue
import Control.Exception (assert)
import Control.Monad (forM, forever, guard, join, unless, void, when, (<=<))
import Control.Tracer (Contravariant (contramap), Tracer, traceWith)
import Data.Bifunctor (second)
import Data.Foldable (forM_)
import Data.Kind
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
import Network.TypedProtocol.Driver (runPeerWithDriver)
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import Numeric.Natural
import PraosProtocol.Common
import qualified PraosProtocol.Common.AnchoredFragment as AnchoredFragment
import qualified PraosProtocol.Common.Chain as Chain

data BlockFetchState (body :: Type)
  = StIdle
  | StBusy
  | StStreaming
  | StDone
  deriving (Show)

data SingBlockFetchState :: forall body. BlockFetchState body -> Type where
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
  forall body (st :: BlockFetchState body) (st' :: BlockFetchState body).
  (StateTokenI st, StateTokenI st') =>
  Maybe (st :~: st')
decideBlockFetchState = decideSingBlockFetchState stateToken stateToken

instance Protocol (BlockFetchState body) where
  data Message (BlockFetchState body) from to where
    MsgRequestRange ::
      Point (Block body) ->
      Point (Block body) ->
      Message (BlockFetchState body) StIdle StBusy
    MsgNoBlocks ::
      Message (BlockFetchState body) StBusy StIdle
    MsgStartBatch ::
      Message (BlockFetchState body) StBusy StStreaming
    MsgBlock ::
      body ->
      Message (BlockFetchState body) StStreaming StStreaming
    MsgBatchDone ::
      Message (BlockFetchState body) StStreaming StIdle
    MsgClientDone ::
      Message (BlockFetchState body) StIdle StDone
  type StateAgency StIdle = ClientAgency
  type StateAgency StBusy = ServerAgency
  type StateAgency StStreaming = ServerAgency
  type StateAgency StDone = NobodyAgency
  type StateToken = SingBlockFetchState

instance StateTokenI StIdle where stateToken = SingStIdle
instance StateTokenI StBusy where stateToken = SingStBusy
instance StateTokenI StStreaming where stateToken = SingStStreaming
instance StateTokenI StDone where stateToken = SingStDone

deriving instance Show body => Show (Message (BlockFetchState body) from to)

instance MessageSize body => MessageSize (Message (BlockFetchState body) st st') where
  messageSizeBytes = \case
    MsgRequestRange pt1 pt2 -> messageSizeBytes pt1 + messageSizeBytes pt2
    MsgNoBlocks -> 1
    MsgStartBatch -> 1
    MsgBlock blk -> messageSizeBytes blk
    MsgBatchDone -> 1
    MsgClientDone -> 1

blockFetchMessageLabel :: Message (BlockFetchState body) st st' -> String
blockFetchMessageLabel = \case
  MsgRequestRange _ _ -> "MsgRequestRange"
  MsgNoBlocks -> "MsgNoBlocks"
  MsgStartBatch -> "MsgStartBatch"
  MsgBlock _ -> "MsgBlock"
  MsgBatchDone -> "MsgBatchDone"
  MsgClientDone -> "MsgClientDone"

type BlockFetchMessage body = ProtocolMessage (BlockFetchState body)

--------------------------------
--- BlockFetch Server
--------------------------------

newtype BlockFetchProducerState body m = BlockFetchProducerState
  { blocksVar :: ReadOnly (TVar m (Blocks body))
  }

runBlockFetchProducer :: (IsBody body, MonadSTM m) => Chan m (BlockFetchMessage body) -> BlockFetchProducerState body m -> m ()
runBlockFetchProducer chan blockFetchProducerState =
  void $ runPeerWithDriver (chanDriver decideBlockFetchState chan) (blockFetchProducer blockFetchProducerState)

resolveRange ::
  forall body m.
  (IsBody body, MonadSTM m) =>
  BlockFetchProducerState body m ->
  Point (Block body) ->
  Point (Block body) ->
  STM m (Maybe [body])
resolveRange st start end = do
  blocks <- readReadOnlyTVar st.blocksVar
  let resolveRangeAcc :: [body] -> Point (Block body) -> Maybe [body]
      resolveRangeAcc _acc bpoint | pointSlot start > pointSlot bpoint = Nothing
      resolveRangeAcc acc GenesisPoint = assert (start == GenesisPoint) (Just acc)
      resolveRangeAcc acc bpoint@(BlockPoint pslot phash) = do
        Block{..} <- Map.lookup phash blocks
        guard $ blockSlot blockHeader == pslot
        let acc' = blockBody : acc
        if start == bpoint
          then Just acc'
          else resolveRangeAcc acc' =<< blockPrevPoint blocks blockHeader
  return $ resolveRangeAcc [] end

blockFetchProducer ::
  forall body m.
  (IsBody body, MonadSTM m) =>
  BlockFetchProducerState body m ->
  TS.Server (BlockFetchState body) NonPipelined StIdle m ()
blockFetchProducer st = idle
 where
  idle :: TS.Server (BlockFetchState body) NonPipelined StIdle m ()
  idle = TS.Await $ \case
    MsgRequestRange start end -> TS.Effect $ atomically $ do
      mblocks <- resolveRange st start end -- Note: we could just look at current chain.
      case mblocks of
        Nothing -> return $ TS.Yield MsgNoBlocks idle
        Just blocks -> return $ TS.Yield MsgStartBatch (streaming blocks)
    MsgClientDone -> TS.Done ()

  streaming :: [body] -> TS.Server (BlockFetchState body) NonPipelined StStreaming m ()
  streaming [] = TS.Yield MsgBatchDone idle
  streaming (block : blocks) = TS.Yield (MsgBlock block) (streaming blocks)

-- NOTE: Variant that uses the current chain.

-- newtype BlockFetchProducerState body m = BlockFetchProducerState
--   { chainVar :: ReadOnly (TVar m (Chain Block))
--   }

-- runBlockFetchProducer :: MonadSTM m => Chan m BlockFetchMessage -> BlockFetchProducerState body m -> m ()
-- runBlockFetchProducer chan blockFetchProducerState =
--   void $ runPeerWithDriver (chanDriver decideBlockFetchState chan) (blockFetchProducer blockFetchProducerState)

-- blockFetchProducer ::
--   forall m.
--   MonadSTM m =>
--   BlockFetchProducerState body m ->
--   TS.Server (BlockFetchState body) NonPipelined StIdle m ()
-- blockFetchProducer st = idle
--  where
--   idle :: TS.Server (BlockFetchState body) NonPipelined StIdle m ()
--   idle = TS.Await $ \case
--     MsgRequestRange start end -> TS.Effect $ atomically $ do
--       bchain <- readReadOnlyTVar st.chainVar
--       case Chain.selectBlockRange bchain start end of
--         Nothing -> return $ TS.Yield MsgNoBlocks idle
--         Just blocks -> return $ TS.Yield MsgStartBatch $ streaming $ (blockBody <$> blocks)
--     MsgClientDone -> TS.Done ()

--   streaming :: [BlockBody] -> TS.Server (BlockFetchState body) NonPipelined StStreaming m ()
--   streaming [] = TS.Yield MsgBatchDone idle
--   streaming (block : blocks) = TS.Yield (MsgBlock block) (streaming blocks)

--------------------------------
--- BlockFetch Client
--------------------------------

newtype BlockRequest
  = BlockRequest {blockRequestFragments :: [AnchoredFragment BlockHeader]}
  deriving (Show)
  deriving newtype (Semigroup) -- TODO: we could merge the fragments.

fragmentRange :: AnchoredFragment BlockHeader -> (Point (Block body), Point (Block body))
fragmentRange fr = (castPoint $ AnchoredFragment.lastPoint fr, castPoint $ AnchoredFragment.headPoint fr)

blockRequestPoints :: BlockRequest -> [Point (Block body)]
blockRequestPoints (BlockRequest frs) = concatMap (map headerPoint . AnchoredFragment.toOldestFirst) frs

data BlockFetchConsumerState body m = BlockFetchConsumerState
  { blockRequestVar :: TVar m BlockRequest
  , addFetchedBlock :: Block body -> m ()
  , submitFetchedBlock :: Block body -> m () -> m ()
  -- ^ a little redundant to have both add and submit, but makes event tracing clearer.
  --   we could pass the peerId instead of `addFetchedBlock` though.
  , removeInFlight :: [Point (Block body)] -> m ()
  }

runBlockFetchConsumer ::
  (IsBody body, Show body, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent body) ->
  PraosConfig body ->
  Chan m (BlockFetchMessage body) ->
  BlockFetchConsumerState body m ->
  m ()
runBlockFetchConsumer tracer cfg chan blockFetchConsumerState =
  void $ runPeerWithDriver (chanDriver decideBlockFetchState chan) (blockFetchConsumer tracer cfg blockFetchConsumerState)

blockFetchConsumer ::
  forall body m.
  (IsBody body, Show body, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent body) ->
  PraosConfig body ->
  BlockFetchConsumerState body m ->
  TC.Client (BlockFetchState body) NonPipelined StIdle m ()
blockFetchConsumer tracer _cfg st = idle
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

  idle :: TC.Client (BlockFetchState body) NonPipelined StIdle m ()
  idle = TC.Effect $ atomically $ do
    fr <- blockRequest
    let range@(start, end) = fragmentRange fr
    return $ TC.Yield (MsgRequestRange start end) $ busy range fr

  busy :: (Point (Block body), Point (Block body)) -> AnchoredFragment BlockHeader -> TC.Client (BlockFetchState body) NonPipelined StBusy m ()
  busy range fr = TC.Await $ \case
    MsgNoBlocks -> TC.Effect $ do
      -- TODO: controller might just ask this peer again.
      st.removeInFlight (blockRequestPoints $ BlockRequest [fr])
      return idle
    MsgStartBatch -> streaming range $ AnchoredFragment.toOldestFirst fr

  streaming :: (Point (Block body), Point (Block body)) -> [BlockHeader] -> TC.Client (BlockFetchState body) NonPipelined StStreaming m ()
  streaming range headers = TC.Await $ \msg ->
    case (msg, headers) of
      (MsgBatchDone, []) -> idle
      (MsgBlock body, header : headers') -> TC.Effect $ do
        let block = Block header body
        traceWith tracer $ PraosNodeEventReceived block
        st.submitFetchedBlock block $ do
          st.addFetchedBlock block
          traceWith tracer (PraosNodeEventEnterState block)

        return $ streaming range headers'
      (MsgBatchDone, _ : _) -> TC.Effect $ error "TooFewBlocks" -- TODO?
      (MsgBlock _, []) -> TC.Effect $ error "TooManyBlocks" -- TODO?

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
    aux x1@(_mpId, c1) (pId, c2) =
      -- We use headHash to refine the order, so that we have less
      -- partitioning in the network.
      -- Actual implementation uses the VRF hash to be adversarial
      -- resistant, but that's not a concern here.
      let measure c = (Chain.headBlockNo c, Chain.headHash c)
       in if measure c1 >= measure c2
            then x1
            else (Just pId, c2)
    -- using foldl' since @selectChain@ is left biased
    (selectedPeer, chain') = List.foldl' aux (Nothing, chain) candidateChains
  return $ do
    peerId <- selectedPeer
    let point = fromMaybe GenesisPoint $ Chain.intersectChains chain chain'
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
--      problem when fetching it.
data PeerStatus body m = PeerStatus
  { blockRequestVar :: TVar m BlockRequest
  , blocksInFlightVar :: TVar m (Set (Point (Block body)))
  , peerChainVar :: ReadOnly (TVar m (Chain BlockHeader))
  }

type PeerId = Int

-- | invariant: blocksVar contains all blocks of cpsVar and targetChainVar
data BlockFetchControllerState body m = BlockFetchControllerState
  { blocksVar :: TVar m (Blocks body)
  , targetChainVar :: TVar m (Maybe (MissingBlocksChain body))
  , peers :: Map PeerId (PeerStatus body m)
  , nextPeerId :: Int
  , cpsVar :: TVar m (ChainProducerState (Block body))
  }

addPeer ::
  forall body m.
  MonadSTM m =>
  ReadOnly (TVar m (Chain BlockHeader)) ->
  BlockFetchControllerState body m ->
  m (BlockFetchControllerState body m, PeerId)
addPeer peerChainVar st = atomically $ do
  let peerId = st.nextPeerId
  blockRequestVar <- newTVar (BlockRequest [])
  blocksInFlightVar <- newTVar Set.empty
  let peerStatus = PeerStatus{..} :: PeerStatus body m
  let peers = Map.insert peerId peerStatus st.peers
  return (st{peers = peers, nextPeerId = peerId + 1}, peerId)

newBlockFetchControllerState :: MonadSTM m => Chain (Block body) -> m (BlockFetchControllerState body m)
newBlockFetchControllerState chain = atomically $ do
  blocksVar <- newTVar (toBlocks chain)
  targetChainVar <- newTVar Nothing
  let peers = Map.empty
  let nextPeerId = 0
  cpsVar <- newTVar $ initChainProducerState chain
  return BlockFetchControllerState{..}

blockFetchController :: forall body m. (IsBody body, MonadSTM m) => Tracer m (PraosNodeEvent body) -> BlockFetchControllerState body m -> m ()
blockFetchController tracer st@BlockFetchControllerState{..} = forever makeRequests
 where
  makeRequests :: m ()
  makeRequests = (traceNewTip tracer =<<) . atomically $ do
    let peerChainVars = (map . second) (.peerChainVar) $ Map.toList peers
    mchainSwitch <- longestChainSelection peerChainVars (asReadOnly cpsVar) blockHeader
    case mchainSwitch of
      Nothing -> retry
      Just (peerId, fragment) -> do
        blocks <- readTVar blocksVar
        chain <- chainState <$> readTVar cpsVar
        let chainUpdate = initMissingBlocksChain blocks chain fragment
        (useful, mtip) <- updateChains st chainUpdate
        whenMissing chainUpdate $ \_missingChain -> do
          -- TODO: filterFetched could be reusing the missingChain suffix.
          br <- filterInFlight <=< filterFetched $ fragment
          if null br.blockRequestFragments
            then unless useful retry
            else addRequest peerId br
        return mtip

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
  addRequest pId br = assert (not $ null br.blockRequestFragments) $ do
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
data MissingBlocksChain body = MissingBlocksChain
  { prefix :: AnchoredFragment (Block body)
  , suffix :: AnchoredFragment (BlockOrHeader body)
  }

newtype BlockOrHeader body = BlockOrHeader {unBlockOrHeader :: Either BlockHeader (Block body)}

type instance HeaderHash (BlockOrHeader body) = HeaderHash BlockHeader

instance StandardHash (BlockOrHeader body)

instance IsBody body => HasHeader (BlockOrHeader body) where
  getHeaderFields (BlockOrHeader x) =
    either
      (castHeaderFields . getHeaderFields)
      (castHeaderFields . getHeaderFields)
      x

headPointMChain :: IsBody body => MissingBlocksChain body -> Point (Block body)
headPointMChain ch = castPoint $ AnchoredFragment.headPoint ch.suffix

data ChainsUpdate body
  = FullChain (Chain (Block body))
  | ImprovedPrefix (MissingBlocksChain body)
  | SamePrefix (MissingBlocksChain body)

fillInBlocks :: forall body. IsBody body => Blocks body -> MissingBlocksChain body -> ChainsUpdate body
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
  blkLookup :: BlockOrHeader body -> BlockOrHeader body
  blkLookup x@(BlockOrHeader e) = case e of
    Right _ -> x
    Left hdr -> maybe x (BlockOrHeader . Right) . Map.lookup (blockHash hdr) $ blocks
  addToChain c (AnchoredFragment.Empty _) = (c, Nothing)
  addToChain c af@(x AnchoredFragment.:< af') = case x of
    BlockOrHeader (Right blk) -> addToChain (c AnchoredFragment.:> blk) af'
    BlockOrHeader (Left _) -> (c, Just af)

initMissingBlocksChain ::
  forall body.
  IsBody body =>
  (Blocks body) ->
  Chain (Block body) ->
  AnchoredFragment BlockHeader ->
  ChainsUpdate body
initMissingBlocksChain blocks c fr =
  fillInBlocks blocks $
    MissingBlocksChain prefix (AnchoredFragment.mapAnchoredFragment (BlockOrHeader . Left) fr)
 where
  pt :: Point (Block body)
  pt = castPoint $ AnchoredFragment.anchorPoint fr
  prefix = case AnchoredFragment.splitAfterPoint (Chain.toAnchoredFragment c) pt of
    Just (before, _) -> before
    Nothing -> error "initMissingBlocksChain: anchor of fragment not on chain"

whenMissing ::
  Monad m =>
  ChainsUpdate body ->
  (MissingBlocksChain body -> m ()) ->
  m ()
whenMissing (FullChain _) _ = return ()
whenMissing (ImprovedPrefix m) k = k m
whenMissing (SamePrefix m) k = k m

-- | Returns whether useful work was done.
updateChains ::
  forall body m.
  (IsBody body, MonadSTM m) =>
  BlockFetchControllerState body m ->
  ChainsUpdate body ->
  STM m (Bool, Maybe (Chain (Block body)))
updateChains BlockFetchControllerState{..} e =
  case e of
    FullChain !fullChain -> do
      writeTVar targetChainVar Nothing
      modifyTVar' cpsVar (switchFork fullChain)
      return (True, Just fullChain)
    ImprovedPrefix missingChain -> do
      writeTVar targetChainVar (Just missingChain)
      let !improvedChain = fromMaybe (error "prefix not from Genesis") $ Chain.fromAnchoredFragment missingChain.prefix
      modifyTVar' cpsVar (switchFork improvedChain)
      return (True, Just improvedChain)
    SamePrefix missingChain -> do
      target <- readTVar targetChainVar
      let useful = Just (headPointMChain missingChain) /= fmap headPointMChain target
      when useful $ do
        writeTVar targetChainVar (Just missingChain)
      return (useful, Nothing)

-----------------------------------------------------------
---- Methods for blockFetchConsumer and blockFetchProducer
-----------------------------------------------------------

removeInFlight :: MonadSTM m => BlockFetchControllerState body m -> PeerId -> [Point (Block body)] -> STM m ()
removeInFlight BlockFetchControllerState{..} pId points = do
  let peer = fromMaybe (error "missing peer") $ Map.lookup pId peers
  modifyTVar' peer.blocksInFlightVar (\s -> List.foldl' (flip Set.delete) s points)

-- | Adds validated block to the state.
--   * removes block from PeerId's in-flight set
--   * adds block to blocksVar
--   * @fillInBlocks@ on @selectedChain@, and @updateChains@
addFetchedBlock :: (IsBody body, MonadSTM m) => Tracer m (PraosNodeEvent body) -> BlockFetchControllerState body m -> PeerId -> Block body -> m ()
addFetchedBlock tracer st pId blk = (traceNewTip tracer =<<) . atomically $ do
  removeInFlight st pId [blockPoint blk]
  modifyTVar' st.blocksVar (Map.insert (blockHash blk) blk)

  selected <- readTVar st.targetChainVar
  case selected of
    Nothing -> return Nothing -- I suppose we do not need this block anymore.
    Just missingChain -> do
      fmap snd $ updateChains st =<< fillInBlocks <$> readTVar st.blocksVar <*> pure missingChain

traceNewTip :: Monad m => Tracer m (PraosNodeEvent body) -> Maybe (Chain (Block body)) -> m ()
traceNewTip tracer x =
  case x of
    Nothing -> return ()
    (Just tip) -> traceWith tracer (PraosNodeEventNewTip tip)

addProducedBlock :: (IsBody body, MonadSTM m) => BlockFetchControllerState body m -> Block body -> STM m ()
addProducedBlock BlockFetchControllerState{..} blk = do
  cps <- readTVar cpsVar
  assert (Chain.validExtension cps.chainState blk) $ do
    writeTVar cpsVar $! addBlock blk cps
    modifyTVar' blocksVar (Map.insert (blockHash blk) blk)

    -- We reset the target chain because ours might be longest now:
    -- the controller will wake up and decide, and we do not want to
    -- switch to the target chain before that.
    writeTVar targetChainVar Nothing

blockRequestVarForPeerId :: PeerId -> BlockFetchControllerState body m -> TVar m BlockRequest
blockRequestVarForPeerId peerId blockFetchControllerState =
  case Map.lookup peerId blockFetchControllerState.peers of
    Nothing -> error $ "blockRequestVarForPeerId: no peer with id " <> show peerId
    Just peerStatus -> peerStatus.blockRequestVar

initBlockFetchConsumerStateForPeerId :: (IsBody body, MonadSTM m) => Tracer m (PraosNodeEvent body) -> PeerId -> BlockFetchControllerState body m -> (Block body -> m () -> m ()) -> BlockFetchConsumerState body m
initBlockFetchConsumerStateForPeerId tracer peerId blockFetchControllerState submitFetchedBlock =
  BlockFetchConsumerState
    (blockRequestVarForPeerId peerId blockFetchControllerState)
    (addFetchedBlock tracer blockFetchControllerState peerId)
    submitFetchedBlock
    (atomically . removeInFlight blockFetchControllerState peerId)

setupValidatorThreads ::
  (MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent BlockBody) ->
  PraosConfig BlockBody ->
  BlockFetchControllerState BlockBody m ->
  -- | bound on queue length.
  Natural ->
  m ([m ()], Block BlockBody -> m () -> m ())
setupValidatorThreads tracer cfg st n = do
  queue <- newTBQueueIO n
  (waitingVar, processWaiting) <- setupProcessWaitingThread (contramap PraosNodeEventCPU tracer) (Just 1) st.blocksVar
  let doTask (delay, m) = do
        traceWith tracer . PraosNodeEventCPU . CPUTask $ delay
        threadDelaySI delay
        m

  -- if we have the previous block, we process the task sequentially to provide back pressure on the queue.
  let waitForPrev block task = case blockPrevHash block of
        GenesisHash -> doTask task
        BlockHash prev -> do
          havePrev <- Map.member prev <$> readTVarIO st.blocksVar
          -- Note: for pure praos this also means we have the ledger state.
          if havePrev
            then doTask task
            else atomically $ modifyTVar' waitingVar (Map.insertWith (++) prev [task])
      fetch = forever $ do
        (block, completion) <- atomically $ readTBQueue queue
        assert (blockInvariant block) $ do
          waitForPrev block $
            let !delay = cfg.blockValidationDelay block
             in (delay, completion)
      add block completion = atomically $ writeTBQueue queue (block, completion)
  return ([fetch, processWaiting], add)

setupProcessWaitingThread ::
  forall m a b.
  (MonadSTM m, MonadDelay m) =>
  Tracer m CPUTask ->
  -- | how many waiting to process in parallel
  Maybe Int ->
  TVar m (Map ConcreteHeaderHash a) ->
  m (TVar m (Map ConcreteHeaderHash [(DiffTime, m b)]), m ())
setupProcessWaitingThread tracer npar blocksVar = do
  waitingVar <- newTVarIO Map.empty
  return $ (waitingVar, processWaiting tracer npar blocksVar waitingVar)

processWaiting ::
  forall m a b.
  (MonadSTM m, MonadDelay m) =>
  Tracer m CPUTask ->
  -- | how many waiting to process in parallel
  Maybe Int ->
  TVar m (Map ConcreteHeaderHash a) ->
  TVar m (Map ConcreteHeaderHash [(DiffTime, m b)]) ->
  m ()
processWaiting tracer npar blocksVar waitingVar = go
 where
  parallelDelay xs = do
    let !d = maximum $ map fst xs
    forM_ xs $ traceWith tracer . CPUTask . fst
    threadDelaySI d
    mapM_ snd xs
  go = forever $ join $ atomically $ do
    waiting <- readTVar waitingVar
    when (Map.null waiting) retry
    blocks <- readTVar blocksVar
    let toValidate = Map.intersection waiting blocks
    when (Map.null toValidate) retry
    writeTVar waitingVar $! waiting Map.\\ toValidate
    let chunks Nothing xs = [xs]
        chunks (Just m) xs = map (take m) . takeWhile (not . null) . iterate (drop m) $ xs
    return $ mapM_ parallelDelay $ chunks npar $ concat $ Map.elems $ toValidate
