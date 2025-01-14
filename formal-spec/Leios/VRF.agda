{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract

module Leios.VRF (a : LeiosAbstract) (let open LeiosAbstract a) where

record VRF (Dom Range PubKey : Type) : Type₁ where
  field isKeyPair : PubKey → PrivKey → Type
        eval : PrivKey → Dom → Range × VrfPf
        verify : PubKey → Dom → Range → VrfPf → Type
        verify? : (pk : PubKey) → (d : Dom) → (r : Range) → (pf : VrfPf) → Dec (verify pk d r pf)

record LeiosVRF : Type₁ where
  field PubKey : Type
        poolID : PubKey → PoolID
        verifySig : PubKey → Sig → Type
        verifySig? : (pk : PubKey) → (sig : Sig) → Dec (verifySig pk sig)

        vrf : VRF ℕ ℕ PubKey

  open VRF vrf public

  -- transforming slot numbers into VRF seeds
  field genIBInput genEBInput genVInput genV1Input genV2Input : ℕ → ℕ

  canProduceIB : ℕ → PrivKey → ℕ → VrfPf → Type
  canProduceIB slot k stake π = let (val , pf) = eval k (genIBInput slot) in val < stake × pf ≡ π

  Dec-canProduceIB : ∀ {slot k stake} → (∃[ π ] canProduceIB slot k stake π) ⊎ (∀ π → ¬ canProduceIB slot k stake π)
  Dec-canProduceIB {slot} {k} {stake} with eval k (genIBInput slot)
  ... | (val , pf) = case ¿ val < stake ¿ of λ where
    (yes p) → inj₁ (pf , p , refl)
    (no ¬p) → inj₂ (λ π (h , _) → ¬p h)

  canProduceIBPub : ℕ → ℕ → PubKey → VrfPf → ℕ → Type
  canProduceIBPub slot val k pf stake = verify k (genIBInput slot) val pf × val < stake

  canProduceEB : ℕ → PrivKey → ℕ → VrfPf → Type
  canProduceEB slot k stake π = let (val , pf) = eval k (genEBInput slot) in val < stake × pf ≡ π

  canProduceEBPub : ℕ → ℕ → PubKey → VrfPf → ℕ → Type
  canProduceEBPub slot val k pf stake = verify k (genEBInput slot) val pf × val < stake

  canProduceV : ℕ → PrivKey → ℕ → Type
  canProduceV slot k stake = proj₁ (eval k (genVInput slot)) < stake

  canProduceV1 : ℕ → PrivKey → ℕ → Type
  canProduceV1 slot k stake = proj₁ (eval k (genV1Input slot)) < stake

  canProduceV2 : ℕ → PrivKey → ℕ → Type
  canProduceV2 slot k stake = proj₁ (eval k (genV2Input slot)) < stake
