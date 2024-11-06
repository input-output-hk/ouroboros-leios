{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract

module Leios.VRF (a : LeiosAbstract) (let open LeiosAbstract a) where

record VRF (Dom Range PubKey : Type) : Type₁ where
  field isKeyPair : PubKey → PrivKey → Type
        eval : PrivKey → Dom → Range × VrfPf
        verify : PubKey → Dom → Range → VrfPf → Type

record LeiosVRF : Type₁ where
  field PubKey : Type
        vrf : VRF ℕ ℕ PubKey

  open VRF vrf public

  -- transforming slot numbers into VRF seeds
  field genIBInput genEBInput : ℕ → ℕ

  canProduceIB : ℕ → PrivKey → ℕ → Type
  canProduceIB slot k stake = proj₁ (eval k (genIBInput slot)) < stake

  canProduceIBPub : ℕ → ℕ → PubKey → VrfPf → ℕ → Type
  canProduceIBPub slot val k pf stake = verify k (genIBInput slot) val pf × val < stake

  canProduceEB : ℕ → PrivKey → ℕ → Type
  canProduceEB slot k stake = proj₁ (eval k (genEBInput slot)) < stake

  canProduceEBPub : ℕ → ℕ → PubKey → VrfPf → ℕ → Type
  canProduceEBPub slot val k pf stake = verify k (genEBInput slot) val pf × val < stake
