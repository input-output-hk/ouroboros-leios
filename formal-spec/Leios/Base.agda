-- {-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract

module Leios.Base (a : LeiosAbstract) (open LeiosAbstract a) where

open import Leios.Blocks a using (EndorserBlock)

StakeDistr : Type
StakeDistr = PoolID ⇀ ℕ

record BaseAbstract : Type₁ where
  field Cert : Type

  data Input : Type₁ where
    INIT   : (EndorserBlock × Cert → Type) → Input
    SUBMIT : EndorserBlock ⊎ List Tx → Input -- maybe we have both

  data Output : Type where
    STAKE : StakeDistr → Output
    EMPTY : Output

  record Functionality : Type₁ where
    field State : Type
          _⇀⟦_⟧_ : State → Input → State × Output → Type
