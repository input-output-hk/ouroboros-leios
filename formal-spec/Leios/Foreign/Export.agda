open import Agda.Builtin.Int
open import Data.Fin
import Data.String as S
open import Data.Char.Base as Char using (Char)
open import Data.Integer using (+_; ∣_∣)

open import Class.Convertible
open import Class.HasHsType
open import Tactic.Derive.Convertible
open import Tactic.Derive.HsType

open import Leios.Prelude
open import Leios.Trace renaming (EndorserBlock to EndorserBlockAgda; IBHeader to IBHeaderAgda)
open import Leios.Foreign.BaseTypes
open import Leios.Foreign.HSTypes
open import Leios.Foreign.Util

module Leios.Foreign.Export where

instance
  HsTy-SlotUpkeep = autoHsType SlotUpkeep ⊣ onConstructors (S.concat ∘ (S.wordsByᵇ ('-' Char.≈ᵇ_)))
  Conv-SlotUpkeep = autoConvert SlotUpkeep

record IBHeader : Type where
  field slotNumber : Int
        producerID : Int

{-# FOREIGN GHC
data IBHeader = IBHeader Integer Integer
  deriving (Show, Eq, Generic)
#-}

{-# COMPILE GHC IBHeader = data IBHeader (IBHeader) #-}

instance
  HsTy-IBHeader = MkHsType IBHeaderAgda IBHeader
  Conv-IBHeader : Convertible IBHeaderAgda IBHeader
  Conv-IBHeader = record
    { to = λ (record { slotNumber = sl ; producerID = pid }) → record { slotNumber = + sl ; producerID = + toℕ pid }
    ; from = λ (record { slotNumber = sl ; producerID = pid }) →
                  record
                    { slotNumber = ∣ sl ∣
                    ; producerID = zero
                    ; lotteryPf = tt
                    ; bodyHash = tt
                    ; signature = tt
                    }
    }

  HsTy-IBBody = autoHsType IBBody
  Conv-IBBody = autoConvert IBBody

  HsTy-InputBlock = autoHsType InputBlock
  Conv-InputBlock = autoConvert InputBlock

  HsTy-Fin = MkHsType PoolID ℕ

  Conv-Fin : HsConvertible PoolID
  Conv-Fin =
    record
      { to = Data.Fin.toℕ
      ; from = λ _ → zero
      }

  Conv-ℕ : HsConvertible ℕ
  Conv-ℕ = Convertible-Refl

record EndorserBlock : Type where
  field slotNumber : Int
        producerID : Int
        ibRefs     : List Int

{-# FOREIGN GHC
data EndorserBlock = EndorserBlock Integer Integer [Integer]
  deriving (Show, Eq, Generic)
#-}

{-# COMPILE GHC EndorserBlock = data EndorserBlock (EndorserBlock) #-}

instance

  HsTy-EndorserBlock = MkHsType EndorserBlockAgda EndorserBlock

  Conv-EndorserBlock : Convertible EndorserBlockAgda EndorserBlock
  Conv-EndorserBlock =
    record
      { to = λ (record { slotNumber = sl ; producerID = pid }) → record { slotNumber = + sl ; producerID = + toℕ pid ; ibRefs = [] }
      ; from = λ (record { slotNumber = sl ; producerID = pid }) →
                    record
                      { slotNumber = ∣ sl ∣
                      ; producerID = zero
                      ; ibRefs = []
                      ; ebRefs = []
                      ; lotteryPf = tt
                      ; signature = tt
                      }
      }

  Listable-Fin : Listable (Fin 1)
  Listable-Fin =
    record
      { listing = singleton zero
      ; complete = λ {a} → (Equivalence.to ∈-singleton) a≡zero
      }
    where
      a≡zero : ∀ {a : Fin 1} → a ≡ zero
      a≡zero {zero} = refl

  HsTy-LeiosState = autoHsType LeiosState
  Conv-LeiosState = autoConvert LeiosState

  HsTy-LeiosInput = autoHsType LeiosInput ⊣ onConstructors (("I_" S.++_) ∘ S.concat ∘ (S.wordsByᵇ ('-' Char.≈ᵇ_)))
  Conv-LeiosInput = autoConvert LeiosInput

  HsTy-LeiosOutput = autoHsType LeiosOutput ⊣ onConstructors (("O_" S.++_) ∘ S.concat ∘ (S.wordsByᵇ ('-' Char.≈ᵇ_)))
  Conv-LeiosOutput = autoConvert LeiosOutput

open import Class.Computational as C
open import Class.Computational22

open Computational22
open BaseAbstract
open FFDAbstract

instance
  Computational-B : Computational22 (BaseAbstract.Functionality._-⟦_/_⟧⇀_ d-BaseFunctionality) String
  Computational-B .computeProof s (INIT x) = success ((STAKE sd , tt) , tt)
  Computational-B .computeProof s (SUBMIT x) = success ((EMPTY , tt) , tt)
  Computational-B .computeProof s FTCH-LDG = success (((BASE-LDG []) , tt) , tt)
  Computational-B .completeness _ _ _ _ _ = error "Computational-B completeness"

  Computational-FFD : Computational22 (FFDAbstract.Functionality._-⟦_/_⟧⇀_ d-FFDFunctionality) String
  Computational-FFD .computeProof s (Send x x₁) = success ((SendRes , tt) , tt)
  Computational-FFD .computeProof s Fetch = success ((FetchRes [] , tt) , tt)
  Computational-FFD .completeness _ _ _ _ _ = error "Computational-FFD completeness"

open import Leios.Short.Deterministic st as D public

stepHs : HsType (LeiosState → LeiosInput → C.ComputationResult String (LeiosOutput × LeiosState))
stepHs = to (compute Computational--⟦/⟧⇀)

{-# COMPILE GHC stepHs as step #-}
