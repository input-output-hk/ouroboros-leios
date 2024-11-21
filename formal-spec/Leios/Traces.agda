{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.SpecStructure

module Leios.Traces (⋯ : SpecStructure) (let open SpecStructure ⋯) where

open import Leios.Protocol (⋯)

module _ (_↝_ : LeiosState → LeiosState → Type) (allUpkeep : ℙ SlotUpkeep) where

  open Rules _↝_ allUpkeep

  _⇉_ : LeiosState → LeiosState → Type
  s₁ ⇉ s₂ = Σ[ (i , o) ∈ LeiosInput × LeiosOutput ] (just s₁ -⟦ i / o ⟧⇀ s₂)

  _⇉[_]_ : LeiosState → ℕ → LeiosState → Type
  s₁ ⇉[ zero ] s₂ = s₁ ≡ s₂
  s₁ ⇉[ suc m ] sₙ = Σ[ s₂ ∈ LeiosState ] (s₁ ⇉ s₂ × s₂ ⇉[ m ] sₙ)

  _⇉⋆_ : LeiosState → LeiosState → Type
  s₁ ⇉⋆ sₙ = Σ[ n ∈  ℕ ] (s₁ ⇉[ n ] sₙ)
