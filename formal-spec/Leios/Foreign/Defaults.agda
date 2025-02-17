{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.SpecStructure
open import Axiom.Set.Properties th

open import Data.Nat.Show as N
open import Data.Integer
open import Data.String as S using (intersperse)
open import Data.Fin
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Structures

import Data.Sum

open Equivalence

-- The module contains very simple implementations for the functionalities
-- that allow to build examples for traces for the different Leios variants
module Leios.Foreign.Defaults where

numberOfParties : ℕ
numberOfParties = 1

SUT-id : Fin numberOfParties
SUT-id = zero

instance
  htx : Hashable (List ℕ) String
  htx = record { hash = S.intersperse "#" ∘ L.map N.show }

d-Abstract : LeiosAbstract
d-Abstract =
  record
    { Tx = ℕ
    ; PoolID = Fin numberOfParties
    ; BodyHash = ⊤
    ; VrfPf = ⊤
    ; PrivKey = ⊤
    ; Sig = ⊤
    ; Hash = String
    ; Vote = ⊤
    ; vote = λ _ _ → tt
    ; sign = λ _ _ → tt
    ; L = 5
    }

open LeiosAbstract d-Abstract public

open import Leios.VRF d-Abstract public

d-VRF : LeiosVRF
d-VRF =
  record
    { PubKey     = ⊤
    ; vrf        = record { isKeyPair = λ _ _ → ⊤ ; eval = λ x x₁ → x₁ , x ; verify = λ _ _ _ _ → ⊤ }
    ; genIBInput = id
    ; genEBInput = id
    ; genVInput  = id
    ; genV1Input = id
    ; genV2Input = id
    }

open LeiosVRF d-VRF public

open import Leios.Blocks d-Abstract public
open import Leios.KeyRegistration d-Abstract d-VRF public

d-KeyRegistration : KeyRegistrationAbstract
d-KeyRegistration = _

d-KeyRegistrationFunctionality : KeyRegistrationAbstract.Functionality d-KeyRegistration
d-KeyRegistrationFunctionality =
  record
    { State = ⊤
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    }

open import Leios.Base d-Abstract d-VRF public

d-Base : BaseAbstract
d-Base =
  record
    { Cert = ⊤
    ; VTy = ⊤
    ; initSlot = λ _ → 0
    ; V-chkCerts = λ _ _ → true
    }

d-BaseFunctionality : BaseAbstract.Functionality d-Base
d-BaseFunctionality =
  record
    { State = ⊤
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    ; SUBMIT-total = tt , tt
    }

open import Leios.FFD public

instance
  isb : IsBlock (List ⊤)
  isb =
    record
      { slotNumber = λ _ → 0
      ; producerID = λ _ → zero
      ; lotteryPf = λ _ → tt
      }

  hhs : ∀ {b} → Hashable (IBHeaderOSig b) String
  hhs = record { hash = IBHeaderOSig.bodyHash }

  hpe : Hashable PreEndorserBlock String
  hpe = record { hash = S.intersperse "#" ∘ EndorserBlockOSig.ibRefs }

record FFDState : Type where
  field inIBs : List InputBlock
        inEBs : List EndorserBlock
        inVTs : List (List Vote)

        outIBs : List InputBlock
        outEBs : List EndorserBlock
        outVTs : List (List Vote)

open GenFFD.Header
open GenFFD.Body
open FFDState

flushIns : FFDState → List (GenFFD.Header ⊎ GenFFD.Body)
flushIns record { inIBs = ibs ; inEBs = ebs ; inVTs = vts } =
  flushIBs ibs ++ L.map (inj₁ ∘ ebHeader) ebs ++ L.map (inj₁ ∘ vHeader) vts
  where
    flushIBs : List InputBlock → List (GenFFD.Header ⊎ GenFFD.Body)
    flushIBs [] = []
    flushIBs (record {header = h; body = b} ∷ ibs) = inj₁ (ibHeader h) ∷ inj₂ (ibBody b) ∷ flushIBs ibs

data SimpleFFD : FFDState → FFDAbstract.Input ffdAbstract → FFDAbstract.Output ffdAbstract → FFDState → Type where
  SendIB : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (ibHeader h) (just (ibBody b))) FFDAbstract.SendRes (record s { outIBs = record {header = h; body = b} ∷ outIBs s})
  SendEB : ∀ {s eb} → SimpleFFD s (FFDAbstract.Send (ebHeader eb) nothing) FFDAbstract.SendRes (record s { outEBs = eb ∷ outEBs s})
  SendVS : ∀ {s vs} → SimpleFFD s (FFDAbstract.Send (vHeader vs) nothing) FFDAbstract.SendRes (record s { outVTs = vs ∷ outVTs s})

  BadSendIB : ∀ {s h} → SimpleFFD s (FFDAbstract.Send (ibHeader h) nothing) FFDAbstract.SendRes s
  BadSendEB : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (ebHeader h) (just b)) FFDAbstract.SendRes s
  BadSendVS : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (vHeader h) (just b)) FFDAbstract.SendRes s

  Fetch : ∀ {s} → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes (flushIns s)) (record s { inIBs = [] ; inEBs = [] ; inVTs = [] })

simple-total : ∀ {s h b} → ∃[ s' ] (SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s')
simple-total {s} {ibHeader h} {just (ibBody b)} = record s { outIBs = record {header = h; body = b} ∷ outIBs s} , SendIB
simple-total {s} {ebHeader eb} {nothing} = record s { outEBs = eb ∷ outEBs s} , SendEB
simple-total {s} {vHeader vs} {nothing} = record s { outVTs = vs ∷ outVTs s} , SendVS

simple-total {s} {ibHeader h} {nothing} = s , BadSendIB
simple-total {s} {ebHeader eb} {just _} = s , BadSendEB
simple-total {s} {vHeader vs} {just _} = s , BadSendVS

d-FFDFunctionality : FFDAbstract.Functionality ffdAbstract
d-FFDFunctionality =
  record
    { State = FFDState
    ; initFFDState = record { inIBs = []; inEBs = []; inVTs = []; outIBs = []; outEBs = []; outVTs = [] }
    ; _-⟦_/_⟧⇀_ = SimpleFFD
    ; FFD-Send-total = simple-total
    }

open import Leios.Voting public

d-VotingAbstract : VotingAbstract (Fin 1 × EndorserBlock)
d-VotingAbstract =
  record
    { VotingState = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

d-VotingAbstract-2 : VotingAbstract (Fin 2 × EndorserBlock)
d-VotingAbstract-2 =
  record
    { VotingState = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

st : SpecStructure 1
st = record
      { a = d-Abstract
      ; id = SUT-id
      ; FFD' = d-FFDFunctionality
      ; vrf' = d-VRF
      ; sk-IB = tt
      ; sk-EB = tt
      ; sk-V = tt
      ; pk-IB = tt
      ; pk-EB = tt
      ; pk-V = tt
      ; B' = d-Base
      ; BF = d-BaseFunctionality
      ; initBaseState = tt
      ; K' = d-KeyRegistration
      ; KF = d-KeyRegistrationFunctionality
      ; va = d-VotingAbstract
      }

st-2 : SpecStructure 2
st-2 = record
      { a = d-Abstract
      ; id = SUT-id
      ; FFD' = d-FFDFunctionality
      ; vrf' = d-VRF
      ; sk-IB = tt
      ; sk-EB = tt
      ; sk-V = tt
      ; pk-IB = tt
      ; pk-EB = tt
      ; pk-V = tt
      ; B' = d-Base
      ; BF = d-BaseFunctionality
      ; initBaseState = tt
      ; K' = d-KeyRegistration
      ; KF = d-KeyRegistrationFunctionality
      ; va = d-VotingAbstract-2
      }

open import Leios.Short st public

sd : TotalMap (Fin numberOfParties) ℕ
sd = record
  { rel = singleton (SUT-id , 1) -- FIXME
  ; left-unique-rel = λ x y →
      let a = cong proj₂ (from ∈-singleton x)
          b = cong proj₂ (from ∈-singleton y)
      in trans a (sym b)
  ; total-rel = total-rel-helper
  }
  where
    total-rel-helper : ∀ {a : Fin 1} → a ∈ dom (singleton (zero , 1))
    total-rel-helper {zero} = to dom∈ (1 , (to ∈-singleton refl))

s₀ : LeiosState
s₀ = initLeiosState tt sd tt
