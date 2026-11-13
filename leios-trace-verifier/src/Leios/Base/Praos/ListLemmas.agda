{-# OPTIONS --safe #-}
{- Generic list machinery for the Praos block tree
   (Leios.Base.Praos.BlockTree):

   - maxBy-mem/-≥       : the fold picking the longest candidate, the
     latest of equally long ones, returns the base or a member, and no
     member is longer;
   - sortDesc-∈/-∈⁻     : sorting a pool by slot keeps exactly its members,
     and sortDesc-sorted : the result is sorted, which is the order the tree
     rebuilds its entries in.

   Everything is measure-generic: μ : A → ℕ is `slot` at the use site,
   ν : B → ℕ is `length`, and σ : B → ℕ, which breaks ties, is the
   adoption number of a chain's tip.
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
open import Data.Nat.Properties using (_≤?_; _<?_; ≤-refl; ≤-reflexive; ≤-trans; <⇒≤; <-trans; <-≤-trans; ≰⇒≥; ≮⇒≥; <-irrefl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no; _⊎-dec_; _×-dec_)
open import Data.Product.Base using (_×_; _,_; proj₁)
import Data.Nat.Properties as ℕ
open import Relation.Nullary.Negation using (¬_; contradiction)

private variable
  A : Set

-- ── Longest element by a measure ────────────────────────────────────────

module MaxBy {B : Set} (ν : B → ℕ) (σ : B → ℕ) where

  -- 'c' displaces 'b' if it is longer, or as long and later.
  Beats : B → B → Set
  Beats b c = ν b < ν c ⊎ (ν b ≡ ν c × σ b < σ c)

  beats? : ∀ b c → Dec (Beats b c)
  beats? b c = (ν b <? ν c) ⊎-dec ((ν b ℕ.≟ ν c) ×-dec (σ b <? σ c))

  beats⇒≤ : ∀ {b c} → Beats b c → ν b ≤ ν c
  beats⇒≤ (inj₁ lt)       = <⇒≤ lt
  beats⇒≤ (inj₂ (eq , _)) = ≤-reflexive eq

  ¬beats⇒≥ : ∀ {b c} → ¬ Beats b c → ν c ≤ ν b
  ¬beats⇒≥ ¬bt = ≮⇒≥ (λ lt → ¬bt (inj₁ lt))

  maxBy : B → List B → B
  maxBy b []       = b
  maxBy b (c ∷ cs) with beats? b c
  ... | yes _ = maxBy c cs
  ... | no  _ = maxBy b cs

  maxBy-mem : ∀ b cs → maxBy b cs ≡ b ⊎ maxBy b cs ∈ cs
  maxBy-mem b [] = inj₁ refl
  maxBy-mem b (c ∷ cs) with beats? b c
  ... | yes _ with maxBy-mem c cs
  ...   | inj₁ e = inj₂ (here e)
  ...   | inj₂ m = inj₂ (there m)
  maxBy-mem b (c ∷ cs) | no _ with maxBy-mem b cs
  ...   | inj₁ e = inj₁ e
  ...   | inj₂ m = inj₂ (there m)

  maxBy-base : ∀ b cs → ν b ≤ ν (maxBy b cs)
  maxBy-base b [] = ≤-refl
  maxBy-base b (c ∷ cs) with beats? b c
  ... | yes bt = ≤-trans (beats⇒≤ bt) (maxBy-base c cs)
  ... | no  _  = maxBy-base b cs

  maxBy-≥ : ∀ b cs {c} → c ∈ cs → ν c ≤ ν (maxBy b cs)
  maxBy-≥ b (c ∷ cs) m with beats? b c | m
  ... | yes _  | here refl = maxBy-base c cs
  ... | yes _  | there m′  = maxBy-≥ c cs m′
  ... | no ¬bt | here refl = ≤-trans (¬beats⇒≥ ¬bt) (maxBy-base b cs)
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

  -- membership is preserved
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

  -- and back: sorting adds nothing
  insert-∈⁻ : ∀ {z} b xs → z ∈ insert b xs → z ∈ b ∷ xs
  insert-∈⁻ b [] p = p
  insert-∈⁻ b (x ∷ xs) p with μ x ≤? μ b
  ... | yes _ = p
  ... | no  _ with p
  ...   | here refl = there (here refl)
  ...   | there q with insert-∈⁻ b xs q
  ...     | here refl = here refl
  ...     | there r   = there (there r)

  sortDesc-∈⁻ : ∀ {z} xs → z ∈ sortDesc xs → z ∈ xs
  sortDesc-∈⁻ (x ∷ xs) p with insert-∈⁻ x (sortDesc xs) p
  ... | here refl = here refl
  ... | there q   = there (sortDesc-∈⁻ xs q)

  Sorted : List A → Set
  Sorted = Lkd.Linked (λ x y → μ y ≤ μ x)

  ltail≤ : ∀ {x xs} → Sorted (x ∷ xs) → Sorted xs
  ltail≤ Lkd.[-]      = Lkd.[]
  ltail≤ (_ Lkd.∷ s) = s

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
