{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE RecordWildCards #-}

module Foo (proposal) where

import           Data.Foldable (foldl')
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified System.Random as Rand
import qualified System.Random.Shuffle as Rand

-----

first :: (a1 -> a2) -> (a1, b) -> (a2, b)
first f = \ ~(x, y) -> (f x, y)

-----

newtype SlotNo = Sl Int                                                         deriving (Eq, Ord, Read, Show)

plus :: SlotNo -> Int -> SlotNo
plus (Sl x) y = Sl $ x + y

-- | This is a unique identifier for the part of the tx that is signed.
--
-- If it were influenced by anything else (eg if it was the hash of the
-- /entire/ transaction, including witnesses etc), then the adversary could
-- alter the contents (eg the order of witnesses) in order to change the 'TxId'
-- when relaying the tx.
--
-- Key invariant: two transactions with the same 'TxId' have the same inputs
-- and outputs. But two transactions with the same 'TxId' do not necessarily
-- have the same validity (that's what the hash of the whole tx including
-- witnesses might be used to record).
newtype TxId u = TX u                                                           deriving (Eq, Ord, Read, Show)

data IbId u = IB SlotNo u                                                       deriving (Eq, Ord, Read, Show)

data EbId u = EB SlotNo u                                                       deriving (Eq, Ord, Read, Show)

-----

-- | Assumed well-formed and non-equivocated in this simple model
newtype IbBody u a b = MkIbBody (Seq (TxId u, TxBody u a b))                    deriving (Eq, Ord, Read, Show)

-- | Assumed well-formed and non-equivocated in this simple model
data EbBody u = MkEbBody (SlotMap u (IbId u)) (SlotMap u (EbId u))              deriving (Eq, Ord, Read, Show)

-----

data TxIn u = MkTxIn (TxId u) Int                                               deriving (Eq, Ord, Read, Show)

-- | Assumed well-formed in this simple model
--
-- These inputs correspond to /spending inputs/. TODO Should it also include
-- withdrawals? TODO Confirm that it should exclude reference inputs.
--
-- * @a@ is metadata about each tx
-- * @b@ is metadata about each tx outputs
--
-- TODO this model doesn't even represent witnesses (eg signatures)
data TxBody u a b = MkTxBody (Set (TxIn u)) [(TxIn u, b)] a                     deriving (Eq, Ord, Read, Show)

meta :: TxBody u a b -> a
meta (MkTxBody _ins _outs x) = x

-----

type SlotMap u v = Map SlotNo (Map u v)

type TxMempool u a b = Seq (TxId u, TxBody u a b)

type IbMempool t u a b l = SlotMap u (Timestamped t (IbBody u a b, Ledger u b))

type EbMempool t u = SlotMap u (Timestamped t (EbBody u))

data Cert = MkCert

data LeiosState t u a b l x = MkLeiosState {
    -- | The ledger state at the tip of the selected RB
    selection :: l
  ,
    -- | Transactions that are cumulatively valid, starting from 'selection',
    -- in arrival order (oldest first)
    txMempool :: TxMempool u a b
  ,
    -- | The ledger state at the tip of 'txMempool'
    txMempoolLedger :: l
  ,
    -- | IBs that have not yet expired, ordered by slot (oldest first) and then
    -- by some objective uniquifier
    --
    -- Annotated with their (oldest) arrival time and their resulting ledger
    -- state in within their current order mempool starting from 'selection'.
    ibMempool :: IbMempool t u a b l
  ,
    -- | Also includes IBs that were evicted from the 'ebMempool', in case
    -- they're referenced by an RB selected later
    allIbs :: SlotMap u (IbBody u a b)
  ,
    -- | EBs that have not yet expired, ordered by slot (oldest first) and then
    -- by some objective uniquifier
    --
    -- Annotated with their (oldest) arrival time.
    ebMempool :: EbMempool t u
  ,
    -- | Also includes EBs that were evicted from the 'ebMempool', in case
    -- they're referenced by an RB selected later
    allEbs :: SlotMap u (EbBody u)
  ,
    certs :: SlotMap u (Timestamped t Cert)
  ,
    -- | Extensible state
    extra :: x
  }

dereferenceEbIds ::
    Ord u
 =>
    SlotMap u (IbBody u a b)
 ->
    SlotMap u (EbBody u)
 ->
    SlotMap u (EbId u)
 ->
    SlotMap u (IbBody u a b)
dereferenceEbIds allIbs allEbs =
    \ebIds ->
        -- TODO smartly defer the 'switchRbs' handler until all of the RB's EBs
        -- and IBs have arrived instead of assuming they already have.
        fromMaybe (error "impossible!")
      $ goEb Set.empty Map.empty ebIds
  where
    goEb !stopEb !acc = (. doubleMinView (\sl u _v -> EB sl u)) $ \case
        Nothing            -> Just acc
        Just (ebId, ebIds) ->
            if ebId `Set.member` stopEb then goEb stopEb acc ebIds else do
                let EB sl u = ebId
                MkEbBody ibIds ebIds' <- Map.lookup sl allEbs >>= Map.lookup u
                acc' <- goIb acc ibIds
                goEb
                    (Set.insert ebId stopEb)
                    acc'
                    (union ebIds ebIds')

    goIb !acc = (. doubleMinView (\sl u _v -> IB sl u)) $ \case
        Nothing               -> Just acc
        Just (IB sl u, ibIds) -> do
            ibBody <- Map.lookup sl allIbs >>= Map.lookup u
            goIb (add sl u ibBody acc) ibIds

-- | This is merely to make some lines shorter in this file
type LeiosEndo t u a b l x =
    LeiosState t u a b l x -> LeiosState t u a b l x

-- | This record captures key methods that are both needed by the Leios node
-- and also dependent on the base ledger rules
data LeiosMethods prng t u a b l x = MkLeiosMethods {
    -- | Given the ledger state at the intersection of the old chain and the
    -- new chain and the slot and included 'EbId's of all subsequent RBs on the
    -- new chain.
    --
    -- (The real ledger also needs at least all of the new RBs' headers, but
    -- this model does not.)
    switchRbs ::
        l -> NonEmpty (SlotNo, SlotMap u (EbId u)) -> LeiosEndo t u a b l x
  ,
    receiveTx :: (TxId u, TxBody u a b) -> LeiosEndo t u a b l x
  ,
    -- | Given the IB's arrival time
    receiveIb :: t -> (IbId u, IbBody u a b) -> LeiosEndo t u a b l x
  ,
    -- | Given the EB's arrival time
    receiveEb :: t -> (EbId u, EbBody u) -> LeiosEndo t u a b l x
  ,
    -- | For convenience, the model does not receive each vote but rather
    -- only the first cert
    --
    -- Given the cert's arrival time.
    receiveCert :: t -> EbId u -> LeiosEndo t u a b l x
  ,
    newIb :: prng -> SlotNo -> LeiosState t u a b l x -> (IbBody u a b, prng)
  ,
    newEb :: SlotNo -> LeiosState t u a b l x -> EbBody u
  ,
    newVt ::
        (SlotNo -> t -> Ordering)
     ->
        SlotNo
     ->
        LeiosState t u a b l x
     ->
        Set (EbId u)
  ,
    newRb :: SlotNo -> LeiosState t u a b l x -> [EbId u]
  }

-----

doubleMax ::
    (Ord k1, Ord k2)
 =>
    Map k1 (Map k2 v)
 ->
    Maybe v
doubleMax m1 = do
    (m2, _rest) <- Map.maxView m1
    (v, _rest) <- Map.maxView m2
    pure v

doubleMinView ::
    (Ord k1, Ord k2)
 =>
    (k1 -> k2 -> v -> a)
 ->
    Map k1 (Map k2 v)
 ->
    Maybe (a, Map k1 (Map k2 v))
doubleMinView f m1 = do
    ((k1, m2), rest1) <- Map.maxViewWithKey m1
    ((k2, v), rest2) <- Map.maxViewWithKey m2
    pure (f k1 k2 v, Map.insertWith Map.union k1 rest2 rest1)

doubleSplit ::
    (Ord k1, Ord k2)
 =>
    k1
 ->
    k2
 ->
    Map k1 (Map k2 v)
 ->
    Either v (Map k1 (Map k2 v), Map k1 (Map k2 v))
doubleSplit k1 k2 m1 =
    case mbEq1 of
        Nothing -> Right (lt1, gt1)
        Just m2 ->
            let (lt2, mbEq2, gt2) = Map.splitLookup k2 m2
            in
            case mbEq2 of
                Just v  -> Left v
                Nothing -> Right (
                    Map.insert k1 lt2 lt1
                  ,
                    Map.insert k1 gt2 gt1
                  )
  where
    (lt1, mbEq1, gt1) = Map.splitLookup k1 m1

reduce :: Foldable t => t a -> (a -> b -> b) -> b -> b
reduce xs snoc nil = foldl' (flip snoc) nil xs

enforceExpiry :: Int -> SlotNo -> (k -> a -> SlotNo) -> Map k a -> Map k a
enforceExpiry expiry sl prj =
    Map.filterWithKey $ \k x -> sl <= plus (prj k x) expiry

add ::
    (Ord k1, Ord k2)
 =>
    k1 -> k2 -> v -> Map k1 (Map k2 v) -> Map k1 (Map k2 v)
add k1 k2 v =
    Map.insertWith
        (\new old -> Map.unionWith const old new)
        k1
        (Map.singleton k2 v)

union ::
    (Ord k1, Ord k2)
 =>
    Map k1 (Map k2 v) -> Map k1 (Map k2 v) -> Map k1 (Map k2 v)
union = Map.unionWith (Map.unionWith const)

mapWithKey ::
    (Ord k1, Ord k2)
 =>
    (k1 -> k2 -> a -> b) -> Map k1 (Map k2 a) -> Map k1 (Map k2 b)
mapWithKey f = Map.mapWithKey (\k1 m2 -> Map.mapWithKey (f k1) m2)

data Timestamped t a = MkTimestamped !t !a

getTimestamped :: Timestamped t a -> a
getTimestamped ~(MkTimestamped _t x) = x

onTimestamped :: (a -> b) -> Timestamped t a -> Timestamped t b
onTimestamped f ~(MkTimestamped t x) = MkTimestamped t (f x)

insert ::
    (Ord k1, Ord k2, Ord t)
 =>
    t
 ->
    k1
 ->
    k2
 ->
    v
 ->
    Map k1 (Map k2 (Timestamped t v))
 ->
    Map k1 (Map k2 (Timestamped t v))
insert t k1 k2 v =
    Map.insertWith
        (\new old -> Map.unionWith f old new)
        k1
        (Map.singleton k2 (MkTimestamped t v))
  where
    f (MkTimestamped t1 x) (MkTimestamped t2 y) =
      MkTimestamped (min t1 t2) (if t2 < t1 then y else x)

-----

-- | Just the UTxO + my penalization idea.
--
-- TODO does the staggering amount of additional logic in the real ledger
-- including anything that disrupts the overall idea of this small model? See
-- 'Cache'.
data Ledger u b = MkLedger {
    -- | A 'TxIn' that either was recently consumed by the recorded 'TxId' or
    -- else would have been recently created by the recorded 'TxId' if it
    -- hadn't been penalized
    offlimits :: Map (TxIn u) (SlotNo, TxId u)
  ,
    tipSlot :: SlotNo
  ,
    utxo :: Map (TxIn u) b
  }

tick :: SlotNo -> Ledger u b -> Ledger u b
tick sl l = l { tipSlot = sl }   -- TODO what else?

-- | Whether a tx has been @Phase2Valid@
--
-- The intention of this cache is to avoid ever running the /scripts/ within a
-- particular tx more than once, regardless of how many times that tx is
-- applied. This reflects the assumption that executing scripts is much much
-- more expensive than looking up UTxO etc.
--
-- A key property the base ledger must provide is that a tx determined to be
-- Phase2Valid against some ledger state (which is impossible unless it's
-- Phase1Valid in that same ledger state, since the Plutus interpreter must be
-- given all /datum/s stored in the subset of the UTxO restricted to /all/ of
-- the tx's inputs) will be Phase2Valid in any state in which its Phase1Valid
-- (even if the ledger states are on different chains, in different slots,
-- etc).
--
-- TODO also cache the "static" checks, eg checking signatures... but that
-- requires a hash of the full tx's bytes, not just the hash of the part of the
-- tx that people sign.
--
-- TODO some notion of age for entries in this cache so that it can be
-- garbage-collected?
newtype Cache u = Cache (Set (TxId u))

cacheInsert :: Ord u => TxId u -> Cache u -> Cache u
cacheInsert txId (Cache xs) = Cache $ Set.insert txId xs

-- | Apply a tx while discarding it is still an option
tryApplyTx ::
    Ord u
 =>
    (Ledger u b, Cache u)
 ->
    (TxId u, TxBody u a b)
 ->
    Maybe (Ledger u b, Cache u)
tryApplyTx (MkLedger{..}, cache) (txId, txBody) =
    if Map.size hits /= Set.size ins then Nothing else
    Just $ flip (,) cache' $ MkLedger {
        -- not updated within the Mempool
        offlimits = offlimits
      ,
        tipSlot = tipSlot
      ,
        utxo = (utxo `Map.difference` hits) `Map.union` Map.fromList outs
      }
  where
    MkTxBody ins outs _ = txBody

    -- TODO also run scripts, unless found in @cache@
    hits = Map.restrictKeys utxo ins

    -- TODO only insert if scripts run and pass
    cache' = cacheInsert txId cache

-- | How to apply a tx when it's too late to discard it
applyTx ::
    Ord u
 =>
    Params
 ->
    (TxId u, TxBody u a b)
 ->
    (Ledger u b, Cache u)
 ->
    (Ledger u b, Cache u)
    -- ^ whether the tx was fully validated
applyTx Params{..} (txId, txBody) (MkLedger{..}, cache) =
    (l', cache')
  where
    MkTxBody ins outs _ = txBody

    hits = Map.restrictKeys utxo ins

    -- TODO switch away from this to the High Collateral scheme
    penalty = not $ Map.null $ Map.restrictKeys offlimits ins

    -- TODO also run scripts, unless found in @cache@
    success = not penalty && Map.size hits == Set.size ins

    blame _ = (tipSlot, txId)

    cache' = (if success then cacheInsert txId else id) cache

    l' = MkLedger {
        offlimits =
            enforceExpiry penaltyExpirySlots tipSlot (\_txIn -> fst)
          $ Map.union offlimits
          $ Map.union (Map.fromSet blame ins)
          $ if not penalty then Map.empty else
            blame <$> Map.fromList outs
      ,
        tipSlot = tipSlot
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
    ibSizeLimit :: TxBytes
  ,
    maxColor :: TxColor
  }

newtype TxBytes = TxBytes Int
  deriving (Eq, Ord, Read, Show)

instance Monoid TxBytes where mempty = TxBytes 0
instance Semigroup TxBytes where TxBytes x <> TxBytes y = TxBytes $ x + y

newtype TxColor = TxColor Int
  deriving (Eq, Ord, Read, Show)

-----

-- | Internal detail of 'extendIbMempool'
data EIB t u a b l = EIB !(IbMempool t u a b l) !l !(Cache u)

extendIbMempool ::
 forall t u a b l x.
    (
        l ~ Ledger u b
    ,
        x ~ Cache u
    ,
        Ord t
    ,
        Ord u
    )
 =>
    Params
 ->
    l
    -- ^ anchor of the existing mempool
 ->
    x
 ->
    IbMempool t u a b l
    -- ^ the existing mempool
 ->
    SlotMap u (Timestamped t (IbBody u a b))
    -- ^ IBs to add
 ->
    (IbMempool t u a b l, x)
extendIbMempool params selection extra0 acc0 ibs =
    let EIB acc' _l' extra' =
            reduce
                (Map.toList ibs)
                (\(sl', m2) ->
                    reduce
                        (Map.toList m2)
                        (\(u', MkTimestamped t (MkIbBody txs)) ->
                            snocIb t (IB sl' u', MkIbBody txs)
                          .
                            reduce txs appTx
                        )
                  .
                    tickIfNecessary sl'
                )
                (EIB acc0 l0 extra0)
    in
    (acc', extra')
  where
    getSlot l = let MkLedger{tipSlot} = l in tipSlot

    l0 = maybe selection (snd . getTimestamped) $ doubleMax acc0

    tickIfNecessary sl' (EIB acc l extra) =
        EIB acc `flip` extra
      $ if getSlot l >= sl' then l else
        tick sl' l

    appTx tx (EIB acc l extra) =
        EIB acc `uncurry` applyTx params tx (l, extra)

    snocIb t (IB sl' u', ibBody') (EIB acc l extra) =
        EIB
            (insert t sl' u' (ibBody', l) acc)
            l
            extra

proposal ::
 forall prng t u a b.
    (a ~ (TxColor, TxBytes), Ord t, Ord u, Rand.RandomGen prng)
 =>
    Params
 ->
    LeiosMethods prng t u a b (Ledger u b) (Cache u)
proposal params@Params{..} =
    MkLeiosMethods {..}
  where
    switchRbs isect rbs MkLeiosState{..} =
        let tipSlot' = fst $ NE.last rbs :: SlotNo

            -- apply the new RB's IB sequence
            (selection', extra1) =
                reduce
                    rbs
                    (\(sl, ebIds) ->
                        reduce
                            (Map.toList $ dereferenceEbIds allIbs allEbs ebIds)
                            (\(_sl', m2) ->
                                 reduce
                                   (Map.toList m2)
                                   (\(_u', MkIbBody txs) ->
                                        -- notice use of the RB slot instead of
                                        -- the IB slot
                                        reduce txs (applyTx params)
                                   )
                            )
                      .
                        first (tick sl)
                    )
                    (isect, extra)

            -- rebuild the 'txMempool'
            --
            -- evict txs that are no longer cumulatively valid starting from
            -- the new 'selection'
            go !acc !accL !accCache = \case
                Seq.Empty      ->
                  (
                    acc :: TxMempool u a b
                  ,
                    accL :: Ledger u b
                  ,
                    accCache :: Cache u
                  )
                tx Seq.:<| txs ->
                    case tryApplyTx (accL, accCache) tx of
                        Nothing                 -> go acc accL accCache txs
                        Just (accL', accCache') ->
                            go (acc Seq.:|> tx ) accL' accCache' txs

            -- TODO which slot to assume? For example, tipSlot+1?
            txMempool'       :: TxMempool u a b
            txMempoolLedger' :: Ledger u b
            extra2           :: Cache u
            (txMempool', txMempoolLedger', extra2) =
                go Seq.Empty selection' extra1 txMempool

            -- rebuild the 'ibMempool'
            --
            -- evict based on age wrt new RB tip (which is merely a lower bound
            -- in this model for the wall clock)
            (ibMempool', extra3) =
                extendIbMempool
                    params
                    selection'
                    extra2
                    Map.empty
                    (
                        Map.map (Map.map (onTimestamped fst))
                      $ enforceExpiry ibExpirySlots tipSlot' const ibMempool
                    )
        in
        MkLeiosState {
            selection = selection'
          ,
            txMempool = txMempool'
          ,
            txMempoolLedger = txMempoolLedger'
          ,
            ibMempool = ibMempool'
          ,
            allIbs = allIbs   -- TODO garbage collect somehow
          ,
            ebMempool = enforceExpiry ebExpirySlots tipSlot' const ebMempool
          ,
            allEbs = allEbs   -- TODO garbage collect somehow
          ,
            certs = enforceExpiry ebExpirySlots tipSlot' const certs
          ,
            extra = extra3   -- TODO garbage collect somehow
          }

    receiveTx tx st@MkLeiosState{..} =
        case tryApplyTx (txMempoolLedger, extra) tx of
            Nothing                         -> st
            Just (txMempoolLedger', extra') -> st {
                extra = extra'
              ,
                txMempool = txMempool Seq.:|> tx
              ,
                txMempoolLedger = txMempoolLedger'
              }

    receiveIb t (IB sl u, ibBody) st@MkLeiosState{..} =
        case doubleSplit sl u ibMempool of
            Left {}        -> st   -- IB already present
            Right (lt, gt) ->
                let gt' =
                        insert t sl u ibBody
                      $ Map.map (Map.map (onTimestamped fst)) gt

                    (ibMempool', extra') =
                        extendIbMempool params selection extra lt gt'
                in
                st {
                    ibMempool = ibMempool'
                  ,
                    allIbs = add sl u ibBody allIbs
                  ,
                    extra = extra'
                  }

    receiveEb t (EB sl u, ebBody) st@MkLeiosState{..} =
        st {
            ebMempool = insert t sl u ebBody ebMempool
          ,
            allEbs = add sl u ebBody allEbs
          }

    receiveCert t (EB sl u) st@MkLeiosState{..} =
        st {
            certs = insert t sl u MkCert certs
          }

    newIb prng _sl MkLeiosState{..} =
        let mempoolColors =
                foldMap (Set.singleton . fst . meta . snd) txMempool

            (prng1, prng2) = Rand.split prng

            l = maybe selection (snd . getTimestamped) $ doubleMax ibMempool

            -- keep the subsequence (not /substring/!) of 'txMempool' that
            -- matches the picked colors and is cumulatively valid starting
            -- from the tip of 'ibMempool'
            goInner !accSz !accTxs !acc !accColors remainingColors = \case
                Seq.Empty      ->
                    goOuter accTxs accColors remainingColors
                tx Seq.:<| txs ->
                    let recur f = f accColors remainingColors txs

                        (txColor, txBytes) = meta $ snd tx

                        hit = txColor `Set.member` accColors

                        tooBig = accSz <> txBytes > ibSizeLimit

                        skip = goInner accSz accTxs acc
                    in
                    if
                      | not hit   -> recur skip
                      | tooBig    -> accTxs
                      | otherwise ->
                        recur
                      $ case tryApplyTx (acc, extra) tx of
                            Nothing              -> skip
                            Just (acc', _extra') ->
                                goInner
                                    (accSz <> txBytes)
                                    (accTxs Seq.:|> tx)
                                    acc'

            -- add colors randomly until the IB is full or the 'txMempool' is
            -- empty
            --
            -- If some red tx depends on a blue tx and red is added before
            -- blue, then 'goInner' will skip that red tx on the red pass but
            -- won't skip it on the red&blue pass. That's why each iteration of
            -- 'goOuter' resets the tx accumulator and works through the
            -- /whole/ 'txMempool' in /its/ actual order.
            goOuter accTxs accColors = \case
                []             -> accTxs
                color : colors ->
                    goInner
                        (TxBytes 0)
                        Seq.empty
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
          (
            MkIbBody $ goOuter Seq.empty Set.empty shuffledColors
          ,
            prng2
          )

    newEb sl MkLeiosState{..} =
        MkEbBody ibIds ebIds
      where
        ibIds =
            mapWithKey (\sl' u' _ibBody -> IB sl' u')
          $ enforceExpiry ibExpirySlots sl const ibMempool

        ebIds =
            mapWithKey (\sl' u' _ebBody -> EB sl' u')
          $ enforceExpiry ebExpirySlots sl const ebMempool

    -- All referenced IBs have been received by the end of the Endorse stage
    -- AND all IBs seen by the end of the Deliver 1 stage are referenced AND
    -- all referenced IBs validate (wrt. script execution) AND only IBs from
    -- this pipeline’s Propose stage are referenced (and not from other
    -- pipelines).
    newVt cmp sl MkLeiosState{..} = error "TODO"

    newRb sl MkLeiosState{..} = error "TODO"
