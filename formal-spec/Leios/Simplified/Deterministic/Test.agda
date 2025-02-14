--------------------------------------------------------------------------------
-- Deterministic variant of simple Leios
--------------------------------------------------------------------------------

open import Leios.Prelude hiding (id)
open import Prelude.Init using (∃₂-syntax)
open import Leios.FFD

import Data.List as L
open import Data.List.Relation.Unary.Any using (here)

open import Leios.SpecStructure
open import Leios.Trace using (st-2)

module Leios.Simplified.Deterministic.Test (Λ μ : ℕ) where

open SpecStructure st-2

import Leios.Simplified
open import Leios.Simplified st-2 Λ μ hiding (_-⟦_/_⟧⇀_) renaming (initLeiosState to initLeiosState')
module ND = Leios.Simplified st-2 Λ μ

open import Class.Computational
open import Class.Computational22
open import StateMachine

open BaseAbstract B' using (Cert; V-chkCerts; VTy; initSlot)
open GenFFD

open FFD hiding (_-⟦_/_⟧⇀_)

private variable s s' s0 s1 s2 s3 s4 s5 : LeiosState
                 i      : LeiosInput
                 o      : LeiosOutput
                 ffds'  : FFD.State
                 π      : VrfPf
                 bs'    : B.State
                 ks ks' : K.State
                 msgs   : List (FFDAbstract.Header ffdAbstract ⊎ FFDAbstract.Body ffdAbstract)
                 eb     : EndorserBlock
                 rbs    : List RankingBlock
                 txs    : List Tx
                 V      : VTy
                 SD     : StakeDistr
                 pks    : List PubKey

open Computational22 ⦃...⦄
open import Leios.Simplified.Deterministic st-2 Λ μ

instance
  Computational-B : Computational22 B._-⟦_/_⟧⇀_ String
  Computational-B .computeProof s (BaseAbstract.Input.INIT x) =
    success ((BaseAbstract.Output.STAKE {!!} , tt) , tt)
  Computational-B .computeProof s (BaseAbstract.Input.SUBMIT x) =
    success ((BaseAbstract.Output.EMPTY , tt) , tt)
  Computational-B .computeProof s BaseAbstract.Input.FTCH-LDG =
    success ((BaseAbstract.Output.BASE-LDG [] , tt) , tt)
  Computational-B .completeness = {!!}

  Computational-FFD : Computational22 FFD._-⟦_/_⟧⇀_ String
  Computational-FFD .computeProof s (FFDAbstract.Send x x₁) = success ((FFDAbstract.SendRes , tt) , tt)
  Computational-FFD .computeProof s FFDAbstract.Fetch       = success ((FFDAbstract.FetchRes [] , tt) , tt)
  Computational-FFD .completeness = {!!}

comp = Computational--⟦/⟧⇀ ⦃ Computational-B ⦄ ⦃ Computational-FFD ⦄

initLeiosState : VTy → StakeDistr → B.State → LeiosState
initLeiosState v sd bs = record (initLeiosState' v sd bs) { Upkeep = allUpkeep }

module _ v sd bs where opaque
  unfolding List-Modelᵈ V2-Role-total

  computeProofTy : (s : LeiosState) (i : LeiosInput)
    → ComputationResult String (Σ[ (o , s') ∈ LeiosOutput × LeiosState ] s -⟦ i / o ⟧⇀ s')
  computeProofTy = computeProof ⦃ comp ⦄

  compute-≡ : (s : LeiosState) (i : LeiosInput)
    → compute ⦃ comp ⦄ s i ≡ map ⦃ Functor-ComputationResult ⦄ proj₁ (computeProof ⦃ comp ⦄ s i)
  compute-≡ s i = refl

  test₁ : ∀ tx
    → Σ[ x ∈ LeiosOutput × LeiosState ] compute (initLeiosState v sd bs) (SUBMIT (inj₂ [ tx ]))
      ≡ success x
  test₁ tx = -, refl

  test₂ : Σ[ x ∈ LeiosOutput × LeiosState ] compute (initLeiosState v sd bs) SLOT
          ≡ success x
  test₂ = -, refl

  test₃ : Tx → Set
  test₃ tx = {!proj₁ test₂!}

  trace : ComputationResult String (List LeiosOutput × LeiosState)
  trace = computeTrace (initLeiosState v sd bs) (SLOT ∷ SLOT ∷ [])
