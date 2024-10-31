open import Leios.Prelude
open import Leios.Abstract

module Leios.BaseFunctionality (a : LeiosAbstract) (let open LeiosAbstract a) where

open import Leios.Blocks a

StakeDistr : Type
StakeDistr = PoolID ⇀ ℕ

postulate Cert : Type

data Input : Type₁ where
  INIT   : (EndorserBlock × Cert → Type) → Input
  SUBMIT : EndorserBlock ⊎ List Tx → Input -- maybe we have both

data Output : Type where
  STAKE : StakeDistr → Output

postulate State  : Type
          _⇀⟦_⟧_ : State → Input → State × Output → Type
