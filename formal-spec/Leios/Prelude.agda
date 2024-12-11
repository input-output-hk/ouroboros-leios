{-# OPTIONS --safe #-}

module Leios.Prelude where

open import abstract-set-theory.FiniteSetTheory public
open import abstract-set-theory.Prelude public
open import Data.List using (upTo)

open import Class.HasAdd public
open import Class.HasOrder public
open import Class.Hashable public
open import Prelude.InferenceRules public

module T where
  open import Data.These public
open T public using (These; this; that)

module L where
  open import Data.List public
open L public using (List; []; _∷_; _++_; catMaybes; head; length; sum; and; or; any)

module A where
  open import Data.List.Relation.Unary.Any public
open A public using (here; there)

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
