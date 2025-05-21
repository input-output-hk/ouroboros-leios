{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE RecordWildCards #-}

module Foo (proposal) where

import           Control.Monad (guard)
import           Data.Foldable (foldl')
import           Data.Traversable (for)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified System.Random as Rand
import qualified System.Random.Shuffle as Rand

-----

newtype SlotNo = Sl Int                                                          deriving (Eq, Ord, Read, Show)

plus :: SlotNo -> Int -> SlotNo
plus (Sl x) y = Sl $ x + y

-- | This is a unique identifier for the part of the tx that is signed.
--
-- If it was influence by anything else (eg it it was the hash of the /entire/
-- transaction, including witnesses etc), then the adversary could alter the
-- contents (eg the order of witnesses) in order to change the 'TxId' when
-- relaying the tx.
--
-- Key invariant: two transactions with the same 'TxId' have the same inputs
-- and outputs. But two transactions with the same 'TxId' do not necessarily
-- have the same validity (that's what the hash of the whole tx including
-- witnesses might be used to record).
newtype TxId u = TX u                                                            deriving (Eq, Ord, Read, Show)

data IbId u = IB SlotNo u                                                        deriving (Eq, Ord, Read, Show)

data EbId u = EB SlotNo u                                                        deriving (Eq, Ord, Read, Show)

-----

-- | Assumed well-formed and non-equivocated in this simple model
newtype IbBody u a b = MkIbBody [(TxId u, TxBody u a b)]                        deriving (Eq, Ord, Read, Show)

-- | Assumed well-formed and non-equivocated in this simple model
data EbBody u = MkEbBody [IbId u] [EbId u]                                      deriving (Eq, Ord, Read, Show)

-----

data TxIn u = MkTxIn (TxId u) Int                                               deriving (Eq, Ord, Read, Show)

-- | Assumed well-formed in this simple model
--
-- These inputs correspond to /spending inputs/. TODO Should it also include
-- withdrawals? TODO Confirm that it should exclude reference inputs.
data TxBody u a b = MkTxBody (Set (TxIn u)) [(TxIn u, b)] a                     deriving (Eq, Ord, Read, Show)

meta :: TxBody u a b -> a
meta (MkTxBody _ins _outs x) = x

-----

data LeiosState u a b l = MkLeiosState {
    -- | The ledger state at the tip of the selected RB
    selection :: l
  ,
    -- | Transactions that are cumulatively valid, starting from 'selection'
    txMempool :: [(TxId u, TxBody u a b)]
  ,
    -- | The ledger state at the tip of 'txMempool'
    txCache   :: l
  ,
    -- | IBs that have not yet expired, ordered by slot and then by arrival
    -- time
    ibMempool :: Map SlotNo [(u, IbBody u a b)]
  ,
    -- | EBs that have not yet expired, ordered by 'EbId'
    ebMempool :: Map SlotNo (Map u (EbBody u))
  ,
    -- | Includes IBs that were evicted from the 'ibMempool', in case an RB
    -- selected later references them
    allIbs    :: Map SlotNo (Map u (IbBody u a b))
  ,
    -- | Includes EBs that were evicted from the 'ebMempool', in case an RB
    -- selected later references them
    allEbs    :: Map SlotNo (Map u (EbBody u))
{-
  ,
    cert1s    :: Map SlotNo (Set u)
  ,
    cert2s    :: Map SlotNo (Set u)
-}
  }

dereferenceEbIds ::
    Ord u
 =>
    LeiosState u a b l
 ->
    [EbId u]
 ->
    [(IbId u, IbBody u a b)]
dereferenceEbIds MkLeiosState{..} =
    \ebIds ->
        -- TODO smartly defer the 'extendWithRb' handler until all of the RB's
        -- EBs and IBs have arrived instead of assuming they already have.
        fromMaybe (error "impossible!")
      $ go Set.empty Set.empty [] ebIds
  where
    go stopIb stopEb acc = \case
        []           -> Just acc
        ebId : ebIds -> do
            let EB sl u = ebId
            MkEbBody ibIds ebIds' <- Map.lookup sl allEbs >>= Map.lookup u
            ibs <- for ibIds $ \ibId -> do
                guard $ not $ ibId `Set.member` stopIb
                let IB sl' u' = ibId
                ibBody <- Map.lookup sl' allIbs >>= Map.lookup u'
                pure (ibId, ibBody)
            go
                (flipflipfoldl' (Set.insert . fst) ibs stopIb)
                (Set.insert ebId stopEb)
                (acc ++ ibs)
                (ebIds' ++ ebIds)

-- | This record captures key methods that are both needed by the Leios node
-- and also dependent on the base ledger rules
data LeiosMethods prng u a b l = MkLeiosMethods {
    -- | The ledger state at the intersection of the old chain and the new
    -- chain, the 'EbId's from all subsequent RBs on the new chain, and the tip
    -- slot of the new chain.
    --
    -- (The real ledger also needs at least all of the new RBs' headers, but
    -- this model does not.)
    switchRbs :: l -> [EbId u] -> SlotNo -> LeiosState u a b l -> LeiosState u a b l
  ,
    receiveTx :: (TxId u, TxBody u a b) -> LeiosState u a b l -> LeiosState u a b l
  ,
    receiveIb :: (IbId u, IbBody u a b) -> LeiosState u a b l -> LeiosState u a b l
  ,
    receiveEb :: (EbId u, EbBody u) -> LeiosState u a b l -> LeiosState u a b l
  ,
    newIb     :: prng -> SlotNo -> LeiosState u a b l -> (IbBody u a b, prng)
{-
  ,
    receiveCert1 :: EbId u -> LeiosState u a b l -> LeiosState u a b l
  ,
    receiveCert2 :: EbId u -> LeiosState u a b l -> LeiosState u a b l
  ,
    newEb        :: SlotNo -> LeiosState u a b l -> EbBody u
  ,
    newVote1     :: SlotNo -> LeiosState u a b l -> Set (EbId u)
  ,
    newVote2     :: SlotNo -> LeiosState u a b l -> Set (EbId u)
  ,
    newRb        :: SlotNo -> LeiosState u a b l -> [EbId u]
-}
  }

-----

-- | Just the UTxO + my penalization idea.
--
-- TODO does the staggering amount of additional logic in the real ledger
-- including anything that disrupts the overall idea of this small model?
data Ledger u b = MkLedger {
    -- | A 'TxIn' that either was recently consumed by the recorded 'TxId' or
    -- else would have been recently created by the recorded 'TxId' if it
    -- hadn't been penalized
    offlimits :: Map (TxIn u) (SlotNo, TxId u)
  ,
    utxo      :: Map (TxIn u) b
  }

data Scrutiny = Apply | Reapply

-- | Apply a tx while discarding it is still an option
maybeApplyTx ::
    Ord u
 =>
    Scrutiny
 ->
    Ledger u b
 ->
    (TxId u, TxBody u meta b)
 ->
    Maybe (Ledger u b)
maybeApplyTx _scenario MkLedger{..} (_txId, txBody) =
    if Map.size hits /= Set.size ins then Nothing else
    Just MkLedger {
        -- not updated within the Mempool
        offlimits = offlimits
      ,
        utxo = (utxo `Map.difference` hits) `Map.union` Map.fromList outs
      }
  where
    MkTxBody ins outs _ = txBody

    -- TODO also run scripts, unless @_scenario@ is 'Reapply'
    hits = Map.restrictKeys utxo ins

-- | How to apply a tx when it's too late to discard it
--
-- TODO should we have a 'Scrutiny' argument here too?
applyTx ::
    Ord u
 =>
    Params
 ->
    SlotNo
 ->
    (TxId u, TxBody u meta b)
 ->
    Ledger u b
 ->
    Ledger u b
applyTx Params{..} sl (txId, txBody) MkLedger{..} =
    MkLedger {
        offlimits =
            enforceExpiry penaltyExpirySlots sl (\_txIn -> fst)
          $ Map.union offlimits
          $ Map.union (Map.fromSet blame ins)
          $ if not penalty then Map.empty else
            blame <$> Map.fromList outs
       ,
        utxo =
          if
            | penalty ->
              utxo `Map.difference` hits
            | success ->
              (utxo `Map.difference` hits) `Map.union` Map.fromList outs
            | otherwise ->
              utxo
      }
  where
    MkTxBody ins outs _ = txBody

    hits = Map.restrictKeys utxo ins

    penalty = not $ Map.null $ Map.restrictKeys offlimits ins

    -- TODO also run scripts
    success = not penalty && Map.size hits == Set.size ins

    blame _ = (sl, txId)

-----

data Params = Params {
    -- | Upper bound on slots between 'selection' and an IB relevant to 'newIb' and 'newEb'
    ibExpirySlots :: Int
  ,
    -- | Upper bound on slots between 'selection' and an EB relevant to 'newEb' and 'newRb'
    ebExpirySlots :: Int
  ,
    -- | How long the ledger remembers that the use of some 'TxIn' incurs a penalty
    penaltyExpirySlots :: Int
  ,
    ibSizeLimit :: TxSize
  ,
    maxColor :: TxColor
  }

newtype TxSize = TxSize Int
  deriving (Eq, Ord, Read, Show)

instance Monoid TxSize where mempty = TxSize 0
instance Semigroup TxSize where TxSize x <> TxSize y = TxSize $ x + y

newtype TxColor = TxColor Int
  deriving (Eq, Ord, Read, Show)

flipflipfoldl' :: Foldable t => (a -> b -> b) -> t a -> b -> b
flipflipfoldl' snoc xs nil = foldl' (\acc x -> snoc x acc) nil xs

enforceExpiry :: Int -> SlotNo -> (k -> a -> SlotNo) -> Map k a -> Map k a
enforceExpiry expiry sl prj =
    Map.filterWithKey $ \k x -> sl <= plus (prj k x) expiry

insertMappend :: (Ord k, Monoid m) => k -> m -> Map k m -> Map k m
insertMappend = Map.insertWith (\new old -> old <> new)

-----

proposal ::
    (Ord u, Rand.RandomGen prng)
 =>
    Params
 ->
    LeiosMethods prng u (TxColor, TxSize) b (Ledger u b)
proposal params@Params{..} =
    MkLeiosMethods {..}
  where
    switchRbs isect ebIds sl st@MkLeiosState{..} =
        let l =
                flipflipfoldl'
                    (\(IB sl' _u, MkIbBody txs) ->
                        flipflipfoldl' (applyTx params sl') txs
                    )
                    (dereferenceEbIds st ebIds)
                    isect

            -- evict txs that are no longer cumulatively valid starting from
            -- the new 'selection'
            go acc1 !acc2 = \case
                []     -> (reverse acc1, acc2)
                tx:txs ->
                    let scenario =
                            Apply   -- TODO check 'txMempool' membership?
                    in
                    case maybeApplyTx scenario acc2 tx of
                        Nothing    -> go       acc1  acc2  txs
                        Just acc2' -> go (tx : acc1) acc2' txs

            (txMempool', txCache') = go [] l txMempool
        in
        MkLeiosState {
            selection = l
          ,
            txMempool = txMempool'
          ,
            txCache = txCache'
          ,
            ibMempool = enforceExpiry ibExpirySlots sl const ibMempool
          ,
            ebMempool = enforceExpiry ebExpirySlots sl const ebMempool
          ,
            allIbs = allIbs   -- TODO garbage collect somehow
          ,
            allEbs = allEbs   -- TODO garbage collect somehow
{-
          ,
            cert1s = enforceExpiry ebExpirySlots sl const cert1s
          ,
            cert2s = enforceExpiry ebExpirySlots sl const cert2s
-}
          }

    receiveTx tx st@MkLeiosState{..} =
        let (txMempool', txCache') =
                case maybeApplyTx Apply txCache tx of
                    Nothing -> (txMempool        , txCache)
                    Just l  -> (txMempool ++ [tx], l      )
        in
        st {
            txMempool = txMempool'
          ,
            txCache = txCache'
          }

    -- TODO do we need to be doing the CPU intensive work as IBs arrive?
    receiveIb (IB sl u, ibBody) st@MkLeiosState{..} =
        st {
            ibMempool = insertMappend sl [(u, ibBody)] ibMempool
          ,
            allIbs = insertMappend sl (Map.singleton u ibBody) allIbs
          }

    receiveEb (EB sl u, ebBody) st@MkLeiosState{..} =
        st {
            ebMempool = insertMappend sl (Map.singleton u ebBody) ebMempool
          ,
            allEbs = insertMappend sl (Map.singleton u ebBody) allEbs
          }

    newIb prng _sl MkLeiosState{..} =
        let mempoolColors =
                foldMap (Set.singleton . fst . meta . snd) txMempool

            (prng1, prng2) = Rand.split prng

            -- reapply the entire 'ibMempool'
            --
            -- If IBs that arrived were simply added to the tip, it'd be cheap
            -- to maintain. But that's not the case, so we just re-evaluate
            -- them all. There are to do this as incrementally as possible even
            -- with IBs arriving out of order, but this code suffices for a
            -- specification.
            l =
                flipflipfoldl'
                    (\(sl', ibBodies) ->
                        flipflipfoldl'
                            (\(_ibId, MkIbBody txs) ->
                                flipflipfoldl' (applyTx params sl') txs
                            )
                            ibBodies
                    )
                    (Map.toList ibMempool)
                    selection

            -- keep the subsequence (not /substring/!) of 'txMempool' that
            -- matches the picked colors and is cumulatively valid starting
            -- from the tip of 'ibMempool'
            goInner !accSz accTxs !acc !accColors remainingColors = \case
                []       ->
                    goOuter accTxs accColors remainingColors
                tx : txs ->
                    let recur f = f accColors remainingColors txs

                        (txColor, txSize) = meta $ snd tx

                        hit = txColor `Set.member` accColors

                        tooBig = accSz <> txSize > ibSizeLimit

                        skip = goInner accSz accTxs acc
                    in
                    if
                      | not hit   -> recur skip
                      | tooBig    -> reverse accTxs
                      | otherwise ->
                        recur
                      $ case maybeApplyTx Reapply acc tx of
                            Nothing   -> skip
                            Just acc' ->
                                goInner
                                    (accSz <> txSize)
                                    (tx : accTxs)
                                    acc'

            -- add colors randomly until the IB is full or the 'txMempool' is
            -- empty
            --
            -- If some red tx depends on a blue tx and red is added before
            -- blue, then 'goInner' will skip that red tx on the red pass but
            -- won't skip it on the red&blue pass. That's why each iteration of
            -- 'goOuter' resets the tx-ish accumulators and works through the
            -- whole 'txMempool' in its actual order.
            goOuter accTxs accColors = \case
                []             -> reverse accTxs
                color : colors ->
                    goInner
                        (TxSize 0)
                        []
                        l
                        (Set.insert color accColors)
                        colors
                        txMempool

            shuffledColors =
                Rand.shuffle'
                    (Set.toList mempoolColors)
                    (Set.size mempoolColors)
                    prng1
        in
        (MkIbBody $ goOuter [] Set.empty shuffledColors, prng2)

{-
    receiveCert1 (EB sl u) st@MkLeiosState{..} =
        st {
            cert1s = insertMappend sl (Set.singleton u) cert1s
          }

    receiveCert2 (EB sl u) st@MkLeiosState{..} =
        st {
            cert2s = insertMappend sl (Set.singleton u) cert2s
          }

    newEb = undefined   -- TODO refer to spec

    newVote1 = undefined   -- TODO refer to spec

    newVote2 = undefined   -- TODO refer to spec

    newRb = undefined   -- TODO refer to spec
-}
