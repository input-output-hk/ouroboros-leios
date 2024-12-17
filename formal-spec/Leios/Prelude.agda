{-# OPTIONS --safe #-}

module Leios.Prelude where

open import abstract-set-theory.FiniteSetTheory public
open import abstract-set-theory.Prelude public
open import Data.List using (upTo)

open import Class.HasAdd public
open import Class.HasOrder public
open import Class.Hashable public
open import Prelude.InferenceRules public

import Data.List as L

fromTo : ℕ → ℕ → List ℕ
fromTo m n = map (_+ m) (upTo (n ∸ m))

slice : (L : ℕ) → ⦃ NonZero L ⦄ → ℕ → ℕ → ℙ ℕ
slice L s x = fromList (fromTo s' (s' + (L ∸ 1)))
  where s' = ((s / L) ∸ x) * L -- equivalent to the formula in the paper

filter : {A : Set} → (P : A → Type) ⦃ _ : P ⁇¹ ⦄ → List A → List A
filter P = L.filter ¿ P ¿¹

instance
  IsSet-List : {A : Set} → IsSet (List A) A
  IsSet-List .toSet A = fromList A

open import Data.List.Relation.Unary.Any
open Properties

finite⇒A≡∅⊎∃a∈A : {X : Type} → {A : ℙ X} → finite A → (A ≡ᵉ ∅) ⊎ Σ[ a ∈ X ] a ∈ A
finite⇒A≡∅⊎∃a∈A ([]    , h) = inj₁ (∅-least (λ a∈A → ⊥-elim (case Equivalence.to h a∈A of λ ())))
finite⇒A≡∅⊎∃a∈A (x ∷ _ , h) = inj₂ (x , Equivalence.from h (here refl))
