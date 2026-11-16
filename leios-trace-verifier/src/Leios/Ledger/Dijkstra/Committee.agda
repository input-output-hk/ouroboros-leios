{- Module: Leios.Ledger.Dijkstra.Committee

   The Leios voting committee as the Dijkstra ledger specification selects
   it ('selectCommittee': the 'leiosCommitteeSize' pools with the most stake,
   each seat weighted by its pool's share of the total stake), and its
   coherence with the stake distribution of the Praos base layer.

   The maintainer's requirement is that Linear Leios's committee stake is
   Praos's stake distribution.  Here the ledger's pool distribution
   'pd : KeyHash ⇀ Coin' is the source, and 'praosStake' is the 'StakeDistr'
   (a total map over the party indices 'Fin n') that the chain driver feeds
   to Praos as 'stake₀'.  Proved below:

   - 'committee-seated': every seat's pool is a registered pool, and its
     weight is 'share' of its pool, the pool's stake over the total stake of
     'pd' (zero for a pool without stake);
   - 'seat-weight': a seat whose pool has stake c in 'pd' weighs
     clamp (c / total);
   - 'positive⇒staked': a seat of positive weight belongs to a pool with
     stake in 'pd'.  Seats of zero weight are possible: 'selectCommittee'
     seats registered pools ('pools'), not staked ones, so when
     'leiosCommitteeSize' exceeds the number of staked pools, registered
     pools without stake fill the remaining seats with weight 0;
   - 'seat-weight-praos': a seat whose pool is party i and has stake weighs
     clamp (lookup praosStake i / total), so the committee weight *is* the
     party's Praos stake share.

   Not proved: that 'totalStake pd' equals the Praos total
   (the sum of 'praosStake' over all parties).  It holds when 'keyOf' is
   injective and covers the support of 'pd'; the proof needs a lemma on
   'indexedSumᵛ'' over 'fromList' that neither library provides.

   Disagreement with leios-spec: leios-spec decides membership by
   'Leios.Config.inVotingCommittee params (stake s)', stake-coverage
   truncation by σc (σc-num / σc-den: all pools whose richer pools do not yet
   cover σc of the stake, ties at the boundary included), from the SUT's
   stake alone.  Dijkstra takes a fixed number of seats ('leiosCommitteeSize',
   ties broken by key hash) and additionally requires an honoured BLS key for
   a seat to sign.  The two agree only for parameters where the σc prefix
   happens to have 'leiosCommitteeSize' pools and no tie straddles the
   boundary.  'inLedgerCommittee' is the Dijkstra predicate in the shape
   leios-spec's 'CanVote' would need; 'CanVote' hard-wires
   'inVotingCommittee', so using it is a spec change, not an instance choice.
-}
{-# OPTIONS --safe #-}

open import Ledger.Dijkstra.Specification.Gov.Base using (GovStructure)

module Leios.Ledger.Dijkstra.Committee (gs : GovStructure) (open GovStructure gs) where

open import Ledger.Prelude
open import Ledger.Prelude.Numeric.UnitInterval
  using (UnitInterval; clamp; fromUnitInterval; _<ᵘⁱ_; 0ᵘⁱ)
open import Ledger.Dijkstra.Specification.Certs gs using (Pools)
open import Ledger.Dijkstra.Specification.Leios gs
  using (LeiosSeat; LeiosCommittee; selectCommittee)

open import Leios.Prelude using (completeFin; maximalFin)
open import Data.Fin using (Fin)

import Data.Rational.Properties as ℚ
open import Data.Maybe using (Is-just)
import Data.Maybe.Relation.Unary.Any as MAny
open import Data.List.Relation.Unary.All using () renaming (All to Allˡ; tabulate to tabulateˡ; lookup to All-lookup)
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.Any using () renaming (Any to Anyˡ)
open import Data.List.Relation.Binary.Permutation.Propositional using (↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭)
open import Relation.Binary.Bundles using (DecTotalOrder)
import Data.List.Sort as Sort

open LeiosSeat
open Equivalence

private
  -- Sorting does not lose a property of all elements.
  All-sort : ∀ {p} (O : DecTotalOrder 0ℓ 0ℓ 0ℓ) {P : DecTotalOrder.Carrier O → Type p}
    {xs} → Allˡ P xs → Allˡ P (Sort.sort O xs)
  All-sort O {xs = xs} = All-resp-↭ (↭-sym (Sort.sort-↭ O xs))

  -- The two eliminations of the Maybe-'if' used by 'selectCommittee'.
  if-just : ∀ {A B : Type} (m : Maybe A) {a} {t : A → B} {f : B}
    → m ≡ just a → (if m then (λ {x} → t x) else f) ≡ t a
  if-just (just _) refl = refl

  if-nothing-0 : ∀ {A : Type} (m : Maybe A) {t : A → UnitInterval} {w}
    → (if m then (λ {x} → t x) else 0ᵘⁱ) ≡ w → 0ᵘⁱ <ᵘⁱ w → Is-just m
  if-nothing-0 (just a) _    _  = MAny.just tt
  if-nothing-0 nothing  refl lt = ⊥-elim (ℚ.<-irrefl refl lt)

module _ (pp : PParams) (e : Epoch) (pd : KeyHash ⇀ Coin) (pools : Pools) where

  totalStake : Coin
  totalStake = ∑[ c ← pd ] c

  -- A pool's weight as 'selectCommittee' computes it: its share of the total
  -- stake, or zero if it has none.
  share : KeyHash → UnitInterval
  share kh = if lookupᵐ? pd kh then (λ {c} → clamp (c /₀ totalStake)) else 0ᵘⁱ

  committee : LeiosCommittee
  committee = selectCommittee pp e pd pools

  Seated : LeiosSeat → Type
  Seated s = s .pool ∈ dom (pools ˢ) × s .weight ≡ share (s .pool)

  committee-seated : Allˡ Seated committee
  committee-seated =
    AllP.take⁺ _ $ All-sort _ $ AllP.map⁺ $ tabulateˡ λ x∈ →
      case from ∈-map (setToList-∈ x∈) of λ where
        ((kh , spp) , refl , kspp∈) → to dom∈ (spp , kspp∈) , refl

  seat-registered : ∀ {s} → s ∈ˡ committee → s .pool ∈ dom (pools ˢ)
  seat-registered s∈ = proj₁ (All-lookup committee-seated s∈)

  seat-weight : ∀ {s c} → s ∈ˡ committee → (s .pool , c) ∈ pd ˢ
    → s .weight ≡ clamp (c /₀ totalStake)
  seat-weight {s} s∈ pc∈ =
    trans (proj₂ (All-lookup committee-seated s∈))
          (if-just (lookupᵐ? pd (s .pool)) (∈⇒lookup≡just pd (s .pool) pc∈))

  private
    just⇒∈dom : ∀ {kh} ⦃ d : (kh ∈ dom (pd ˢ)) ⁇ ⦄ → Is-just (lookupᵐ? pd kh ⦃ d ⦄) → kh ∈ dom (pd ˢ)
    just⇒∈dom ⦃ ⁇ yes p ⦄ _ = p
    just⇒∈dom ⦃ ⁇ no _ ⦄ ()

  positive⇒staked : ∀ {s} → s ∈ˡ committee → 0ᵘⁱ <ᵘⁱ s .weight → s .pool ∈ dom (pd ˢ)
  positive⇒staked {s} s∈ pos =
    just⇒∈dom (if-nothing-0 (lookupᵐ? pd (s .pool))
                            (sym (proj₂ (All-lookup committee-seated s∈))) pos)

  -- The Praos side: parties 'Fin n', each the pool 'keyOf i'.
  module Praos {n : ℕ} (keyOf : Fin n → KeyHash) where

    open FunTot (completeFin n) (maximalFin n)

    -- The stake of party i, as the chain driver hands it to Praos ('stake₀')
    -- and to Linear Leios ('SD').
    praosStake : TotalMap (Fin n) ℕ
    praosStake = Fun⇒TotalMap λ i → maybe id 0 (lookupᵐ? pd (keyOf i))

    praosStake-lookup : ∀ {i c} → (keyOf i , c) ∈ pd ˢ → TotalMap.lookup praosStake i ≡ c
    praosStake-lookup {i} kc∈ =
      trans lookup∘Fun⇒TotalMap-id
            (cong (maybe id 0) (∈⇒lookup≡just pd (keyOf i) kc∈))

    seat-weight-praos : ∀ {s i} → s ∈ˡ committee → s .pool ≡ keyOf i → s .pool ∈ dom (pd ˢ)
      → s .weight ≡ clamp (TotalMap.lookup praosStake i /₀ totalStake)
    seat-weight-praos {s} {i} s∈ refl p∈ with from dom∈ p∈
    ... | c , pc∈ = trans (seat-weight s∈ pc∈)
                          (cong (λ x → clamp (x /₀ totalStake)) (sym (praosStake-lookup pc∈)))

    -- Committee membership of party i in Dijkstra's sense, able to sign: it
    -- holds a seat with an honoured BLS key.
    inLedgerCommittee : Fin n → Type
    inLedgerCommittee i = Anyˡ (λ s → s .pool ≡ keyOf i × Is-just (s .key)) committee
