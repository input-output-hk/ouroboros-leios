{-# OPTIONS --safe #-}
{- Generic list machinery for the Praos block-tree instance
   (Leios.Base.Praos.Assumptions).

   The block tree's bestChain enumerates every subsequence of the
   slot-descending sorting of the block pool and keeps the longest valid one.
   These are the pieces that make the Protocol.Tree laws provable:

   - subseqs-complete : every sublist of the sorted pool is enumerated;
   - decr-sub-sorted  : every strictly-decreasing selection from the pool IS
     a sublist of the sorted pool, so the `optimal` law quantifies over
     nothing the enumeration misses;
   - maxBy-mem/-≥     : the fold picking the longest candidate returns the
     base or a member, and no member is longer.

   Everything is measure-generic: μ : A → ℕ is `slot` at the use site and
   ν : B → ℕ is `length`.
-}
module Leios.Base.Praos.ListLemmas where

open import Data.List.Base using (List; []; _∷_; [_]; _++_; map; foldr; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapAll; lookup to lookupAll)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Linked as Lkd
import Data.List.Relation.Binary.Sublist.Propositional as SL
open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (_≤?_; _<?_; ≤-refl; ≤-trans; <⇒≤; <-trans; <-≤-trans; ≰⇒≥; ≮⇒≥; <-irrefl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

private variable
  A : Set

-- ── All subsequences ────────────────────────────────────────────────────

subseqs : List A → List (List A)
subseqs []       = [ [] ]
subseqs (x ∷ xs) = map (x ∷_) (subseqs xs) ++ subseqs xs

subseqs-complete : ∀ {c ys : List A} → c SL.⊆ ys → c ∈ subseqs ys
subseqs-complete {ys = []}     SL.[]         = here refl
subseqs-complete {ys = y ∷ ys} (_ SL.∷ʳ s)   = ∈-++⁺ʳ (map (y ∷_) (subseqs ys)) (subseqs-complete s)
subseqs-complete {ys = y ∷ ys} (refl SL.∷ s) = ∈-++⁺ˡ (∈-map⁺ (y ∷_) (subseqs-complete s))

-- ── Longest element by a measure ────────────────────────────────────────

module MaxBy {B : Set} (ν : B → ℕ) where

  maxBy : B → List B → B
  maxBy b []       = b
  maxBy b (c ∷ cs) with ν b <? ν c
  ... | yes _ = maxBy c cs
  ... | no  _ = maxBy b cs

  maxBy-mem : ∀ b cs → maxBy b cs ≡ b ⊎ maxBy b cs ∈ cs
  maxBy-mem b [] = inj₁ refl
  maxBy-mem b (c ∷ cs) with ν b <? ν c
  ... | yes _ with maxBy-mem c cs
  ...   | inj₁ e = inj₂ (here e)
  ...   | inj₂ m = inj₂ (there m)
  maxBy-mem b (c ∷ cs) | no _ with maxBy-mem b cs
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ m = inj₂ (there m)

  maxBy-base : ∀ b cs → ν b ≤ ν (maxBy b cs)
  maxBy-base b [] = ≤-refl
  maxBy-base b (c ∷ cs) with ν b <? ν c
  ... | yes lt = ≤-trans (<⇒≤ lt) (maxBy-base c cs)
  ... | no  _  = maxBy-base b cs

  maxBy-≥ : ∀ b cs {c} → c ∈ cs → ν c ≤ ν (maxBy b cs)
  maxBy-≥ b (c ∷ cs) m with ν b <? ν c | m
  ... | yes _  | here refl = maxBy-base c cs
  ... | yes _  | there m′  = maxBy-≥ c cs m′
  ... | no ¬lt | here refl = ≤-trans (≮⇒≥ ¬lt) (maxBy-base b cs)
  ... | no _   | there m′  = maxBy-≥ b cs m′

-- ── Descending insertion sort by a measure ──────────────────────────────

module SortDesc {A : Set} (_≟ᴬ_ : ∀ (x y : A) → Dec (x ≡ y)) (μ : A → ℕ) where

  insert : A → List A → List A
  insert b [] = [ b ]
  insert b (x ∷ xs) with μ x ≤? μ b
  ... | yes _ = b ∷ x ∷ xs
  ... | no  _ = x ∷ insert b xs

  sortDesc : List A → List A
  sortDesc = foldr insert []

  -- membership is preserved (this direction is all the laws need)
  insert-∈ : ∀ {z} b xs → z ∈ b ∷ xs → z ∈ insert b xs
  insert-∈ b [] p = p
  insert-∈ b (x ∷ xs) p with μ x ≤? μ b
  ... | yes _ = p
  ... | no  _ with p
  ...   | here refl         = there (insert-∈ b xs (here refl))
  ...   | there (here refl) = here refl
  ...   | there (there q)   = there (insert-∈ b xs (there q))

  sortDesc-∈ : ∀ {z} xs → z ∈ xs → z ∈ sortDesc xs
  sortDesc-∈ (x ∷ xs) (here refl) = insert-∈ x (sortDesc xs) (here refl)
  sortDesc-∈ (x ∷ xs) (there p)   = insert-∈ x (sortDesc xs) (there (sortDesc-∈ xs p))

  Sorted : List A → Set
  Sorted = Lkd.Linked (λ x y → μ y ≤ μ x)

  Decr : List A → Set
  Decr = Lkd.Linked (λ x y → μ y < μ x)

  ltail≤ : ∀ {x xs} → Sorted (x ∷ xs) → Sorted xs
  ltail≤ Lkd.[-]      = Lkd.[]
  ltail≤ (_ Lkd.∷ s) = s

  ltail< : ∀ {x xs} → Decr (x ∷ xs) → Decr xs
  ltail< Lkd.[-]      = Lkd.[]
  ltail< (_ Lkd.∷ s) = s

  sorted⇒All : ∀ {y ys} → Sorted (y ∷ ys) → All (λ z → μ z ≤ μ y) ys
  sorted⇒All Lkd.[-]      = []
  sorted⇒All (r Lkd.∷ s) = r ∷ mapAll (λ q → ≤-trans q r) (sorted⇒All s)

  decr⇒All : ∀ {y ys} → Decr (y ∷ ys) → All (λ z → μ z < μ y) ys
  decr⇒All Lkd.[-]      = []
  decr⇒All (r Lkd.∷ s) = r ∷ mapAll (λ q → <-trans q r) (decr⇒All s)

  insert-sorted : ∀ b xs → Sorted xs → Sorted (insert b xs)
  insert-sorted b [] _ = Lkd.[-]
  insert-sorted b (x ∷ xs) s with μ x ≤? μ b
  ... | yes p = p Lkd.∷ s
  insert-sorted b (x ∷ [])     Lkd.[-]      | no ¬p = ≰⇒≥ ¬p Lkd.∷ Lkd.[-]
  insert-sorted b (x ∷ y ∷ ys) (r Lkd.∷ s) | no ¬p
    with μ y ≤? μ b | insert-sorted b (y ∷ ys) s
  ... | yes q | _  = ≰⇒≥ ¬p Lkd.∷ (q Lkd.∷ s)
  ... | no  _ | ih = r Lkd.∷ ih

  sortDesc-sorted : ∀ xs → Sorted (sortDesc xs)
  sortDesc-sorted []       = Lkd.[]
  sortDesc-sorted (x ∷ xs) = insert-sorted x (sortDesc xs) (sortDesc-sorted xs)

  []⊆ : ∀ (ys : List A) → SL._⊆_ [] ys
  []⊆ []       = SL.[]
  []⊆ (y ∷ ys) = y SL.∷ʳ []⊆ ys

  -- The key completeness fact: a strictly-decreasing selection from a pool
  -- is a sublist of the pool's descending sorting.
  decr-sub-sorted : ∀ {c ys} → Decr c → All (_∈ ys) c → Sorted ys → c SL.⊆ ys
  decr-sub-sorted {[]}     {ys} _ _ _ = []⊆ ys
  decr-sub-sorted {x ∷ c′} {[]} _ (() ∷ _) _
  decr-sub-sorted {x ∷ c′} {y ∷ ys} d (x∈ ∷ a′) s with x ≟ᴬ y
  ... | yes refl = refl SL.∷ decr-sub-sorted (ltail< d) (strip a′ (decr⇒All d)) (ltail≤ s)
    where
      strip : ∀ {zs} → All (_∈ x ∷ ys) zs → All (λ z → μ z < μ x) zs → All (_∈ ys) zs
      strip []                 []       = []
      strip (here refl ∷ _)    (h ∷ _)  = contradiction h (<-irrefl refl)
      strip (there p ∷ ps)     (_ ∷ hs) = p ∷ strip ps hs
  ... | no x≢y = y SL.∷ʳ decr-sub-sorted d (x∈ys ∷ strip′ a′ (decr⇒All d)) (ltail≤ s)
    where
      drop-here : x ∈ y ∷ ys → x ∈ ys
      drop-here (here e)  = contradiction e x≢y
      drop-here (there p) = p

      x∈ys : x ∈ ys
      x∈ys = drop-here x∈

      x≤y : μ x ≤ μ y
      x≤y = lookupAll (sorted⇒All s) x∈ys

      strip′ : ∀ {zs} → All (_∈ y ∷ ys) zs → All (λ z → μ z < μ x) zs → All (_∈ ys) zs
      strip′ []              []       = []
      strip′ (here refl ∷ _) (h ∷ _)  = contradiction (<-≤-trans h x≤y) (<-irrefl refl)
      strip′ (there p ∷ ps)  (_ ∷ hs) = p ∷ strip′ ps hs
