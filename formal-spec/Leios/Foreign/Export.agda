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
open import Leios.Trace
open import Leios.Foreign.BaseTypes
open import Leios.Foreign.HSTypes

module Leios.Foreign.Export where

instance
  HsTy-SlotUpkeep = autoHsType SlotUpkeep ⊣ onConstructors (S.concat ∘ (S.wordsByᵇ ('-' Char.≈ᵇ_)))
  Conv-SlotUpkeep = autoConvert SlotUpkeep

record IBHeaderHs : Type where
  field slotNumber : Int
        producerID : Int

{-# FOREIGN GHC
data IBHeaderHs = IBHeaderHs Integer Integer 
#-}

{-# COMPILE GHC IBHeaderHs = data IBHeaderHs (IBHeaderHs) #-}

instance
  HsTy-IBHeader = MkHsType IBHeader IBHeaderHs
  Conv-IBHeader : Convertible IBHeader IBHeaderHs
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

record EndorserBlockHs : Type where
  field slotNumber : Int
        producerID : Int
        ibRefs     : List Int
        
{-# FOREIGN GHC
data EndorserBlockHs = EndorserBlockHs Integer Integer [Integer]
#-}

{-# COMPILE GHC EndorserBlockHs = data EndorserBlockHs (EndorserBlockHs) #-}

instance

  HsTy-EndorserBlock = MkHsType EndorserBlock EndorserBlockHs
  
  Conv-EndorserBlock : Convertible EndorserBlock EndorserBlockHs
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

  HsTy-LeiosState = autoHsType LeiosState
  Conv-LeiosState = autoConvert LeiosState

