{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Variant of `Computational` for relations with two inputs and outputs
--------------------------------------------------------------------------------

module Class.Computational22 where

open import Leios.Prelude
open import Class.Computational

private variable
  S I O Err : Type

module _ (STS : S → I → O → S → Type) where
  record Computational22 Err : Type₁ where
    constructor MkComputational
    field
      computeProof : (s : S) (i : I) → ComputationResult Err (∃[ (o , s') ] STS s i o s')

    compute : S → I → ComputationResult Err (O × S)
    compute s i = map proj₁ $ computeProof s i

    field
      completeness : ∀ s i o s' → STS s i o s' → compute s i ≡ success (o , s')

  STS' : S × I → O × S → Type
  STS' (s , i) (o , s') = STS s i o s'

  module _ ⦃ _ : Computational22 Err ⦄ where
    open Computational22 it
    instance
      comp22⇒comp : Computational STS' Err
      comp22⇒comp .Computational.computeProof (s , i)          = computeProof s i
      comp22⇒comp .Computational.completeness (s , i) (o , s') = completeness s i o s'

module _ {STS : S → I → O → S → Type} ⦃ _ : Computational22 STS Err ⦄ where
  open Computational22 it

  -- basically `traverse`
  computeTrace : S → List I → ComputationResult Err (List O × S)
  computeTrace s [] = success ([] , s)
  computeTrace s (x ∷ is) = do
    (o , s')   ← compute s x
    (os , s'') ← computeTrace s' is
    return (o ∷ os , s'')
