open import Data.Char.Base as C using (Char)
import Data.String as S
open import Data.Fin using (Fin; toℕ; zero; #_)
open import Data.Integer using (+_; ∣_∣)

open import Class.Convertible
open import Class.HasHsType
open import Tactic.Derive.Convertible
open import Tactic.Derive.HsType

open import Leios.Prelude
open import Leios.Foreign.Defaults
  renaming (EndorserBlock to EndorserBlockAgda; IBHeader to IBHeaderAgda) --  LeiosState to LeiosStateAgda)
open import Leios.Foreign.BaseTypes
open import Leios.Foreign.HsTypes
open import Leios.Foreign.Util

module Leios.Foreign.Types where

{-# FOREIGN GHC
  {-# LANGUAGE DuplicateRecordFields #-}
#-}

dropDash : S.String → S.String
dropDash = S.concat ∘ (S.wordsByᵇ ('-' C.≈ᵇ_))

prefix : S.String → S.String → S.String
prefix p = p S.++_

instance
  HsTy-SlotUpkeep = autoHsType SlotUpkeep ⊣ onConstructors dropDash
  Conv-SlotUpkeep = autoConvert SlotUpkeep

record IBHeader : Type where
  field slotNumber : ℕ
        producerID : ℕ
        bodyHash : String

{-# FOREIGN GHC
data IBHeader = IBHeader {slotNumber :: Integer, producerID :: Integer, bodyHash :: Data.Text.Text }
  deriving (Show, Eq, Generic)
#-}

{-# COMPILE GHC IBHeader = data IBHeader (IBHeader) #-}

instance
  HsTy-IBHeader = MkHsType IBHeaderAgda IBHeader
  Conv-IBHeader : Convertible IBHeaderAgda IBHeader
  Conv-IBHeader = record
    { to = λ (record { slotNumber = s ; producerID = p ; bodyHash = h }) →
        record { slotNumber = s ; producerID = toℕ p ; bodyHash = h}
    ; from = λ (record { slotNumber = s ; producerID = p ; bodyHash = h }) →
        case p <? numberOfParties of λ where
          (yes q) → record { slotNumber = s ; producerID = #_ p {numberOfParties} {fromWitness q} ; lotteryPf = tt ; bodyHash = h ; signature = tt }
          (no _) → error "Conversion to Fin not possible!"
    }

  HsTy-IBBody = autoHsType IBBody
  Conv-IBBody = autoConvert IBBody

  HsTy-InputBlock = autoHsType InputBlock
  Conv-InputBlock = autoConvert InputBlock

  Conv-ℕ : HsConvertible ℕ
  Conv-ℕ = Convertible-Refl

record EndorserBlock : Type where
  field slotNumber : ℕ
        producerID : ℕ
        ibRefs     : List String

{-# FOREIGN GHC
data EndorserBlock = EndorserBlock { slotNumber :: Integer, producerID :: Integer, ibRefs :: [Data.Text.Text] }
  deriving (Show, Eq, Generic)
#-}

{-# COMPILE GHC EndorserBlock = data EndorserBlock (EndorserBlock) #-}

instance

  HsTy-EndorserBlock = MkHsType EndorserBlockAgda EndorserBlock

  Conv-EndorserBlock : Convertible EndorserBlockAgda EndorserBlock
  Conv-EndorserBlock =
    record
      { to = λ (record { slotNumber = s ; producerID = p ; ibRefs = refs }) →
          record { slotNumber = s ; producerID = toℕ p ; ibRefs = refs }
      ; from = λ (record { slotNumber = s ; producerID = p ; ibRefs = refs }) →
        case p <? numberOfParties of λ where
          (yes q) → record { slotNumber = s ; producerID = #_ p {numberOfParties} {fromWitness q} ; lotteryPf = tt ; signature = tt ; ibRefs = refs ; ebRefs = [] }
          (no _) → error "Conversion to Fin not possible!"
      }

  Listable-Fin : Listable (Fin numberOfParties)
  Listable-Fin =
    record
      { listing = singleton zero
      ; complete = λ {a} → (Equivalence.to ∈-singleton) a≡zero
      }
    where
      a≡zero : ∀ {a : Fin numberOfParties} → a ≡ zero
      a≡zero {zero} = refl

  HsTy-FFDState = autoHsType FFDState
  Conv-FFDState = autoConvert FFDState

  HsTy-Fin = MkHsType (Fin numberOfParties) ℕ

  Conv-Fin : HsConvertible (Fin numberOfParties)
  Conv-Fin =
    record
      { to = Data.Fin.toℕ
      ; from = λ p →
                 case p <? numberOfParties of λ where
                   (yes q) → #_ p {numberOfParties} {fromWitness q}
                   (no _) → error "Conversion to Fin not possible!"
      }

  HsTy-LeiosState = autoHsType LeiosState
  Conv-LeiosState = autoConvert LeiosState

  HsTy-LeiosInput = autoHsType LeiosInput ⊣ onConstructors (prefix "I_" ∘ dropDash)
  Conv-LeiosInput = autoConvert LeiosInput

  HsTy-LeiosOutput = autoHsType LeiosOutput ⊣ onConstructors (prefix "O_" ∘ dropDash)
  Conv-LeiosOutput = autoConvert LeiosOutput

open import Class.Computational as C
open import Class.Computational22

open Computational22
open BaseAbstract
open FFDAbstract

open GenFFD.Header using (ibHeader; ebHeader; vHeader)
open GenFFD.Body using (ibBody)
open FFDState

instance
  Computational-B : Computational22 (BaseAbstract.Functionality._-⟦_/_⟧⇀_ d-BaseFunctionality) String
  Computational-B .computeProof s (INIT x) = success ((STAKE sd , tt) , tt)
  Computational-B .computeProof s (SUBMIT x) = success ((EMPTY , tt) , tt)
  Computational-B .computeProof s FTCH-LDG = success (((BASE-LDG []) , tt) , tt)
  Computational-B .completeness _ _ _ _ _ = error "Computational-B completeness"

  Computational-FFD : Computational22 (FFDAbstract.Functionality._-⟦_/_⟧⇀_ d-FFDFunctionality) String
  Computational-FFD .computeProof s (Send (ibHeader h) (just (ibBody b))) = success ((SendRes , record s {outIBs = record {header = h; body = b} ∷ outIBs s}) , SendIB)
  Computational-FFD .computeProof s (Send (ebHeader h) nothing) = success ((SendRes , record s {outEBs = h ∷ outEBs s}) , SendEB)
  Computational-FFD .computeProof s (Send (vHeader h) nothing) = success ((SendRes , record s {outVTs = h ∷ outVTs s}) , SendVS)
  Computational-FFD .computeProof s Fetch = success ((FetchRes (flushIns s) , record s {inIBs = []; inEBs = []; inVTs = []}) , Fetch)

  Computational-FFD .computeProof _ _ = failure "FFD error"
  Computational-FFD .completeness _ _ _ _ _ = error "Computational-FFD completeness"

open import Leios.Short.Deterministic st as D public

stepHs : HsType (LeiosState → LeiosInput → C.ComputationResult String (LeiosOutput × LeiosState))
stepHs = to (compute Computational--⟦/⟧⇀)

{-# COMPILE GHC stepHs as step #-}
