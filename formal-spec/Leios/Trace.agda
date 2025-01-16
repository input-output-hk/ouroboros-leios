{-# OPTIONS --safe #-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.SpecStructure

open import Axiom.Set.Properties th

module Leios.Trace where

instance
  htx : Hashable (List ⊤) ⊤
  htx = record { hash = λ _ → tt }

d-Abstract : LeiosAbstract
d-Abstract =
  record
    { Tx = ⊤
    ; PoolID = ℕ
    ; BodyHash = ⊤
    ; VrfPf = ⊤
    ; PrivKey = ⊤
    ; Sig = ⊤
    ; Hash = ⊤
    ; Vote = ⊤
    ; vote = λ _ _ → tt
    ; sign = λ _ _ → tt
    ; L = 5
    }

open import Leios.VRF d-Abstract

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

open import Leios.Blocks d-Abstract
open import Leios.KeyRegistration d-Abstract d-VRF

d-KeyRegistration : KeyRegistrationAbstract
d-KeyRegistration = _

d-KeyRegistrationFunctionality : KeyRegistrationAbstract.Functionality d-KeyRegistration
d-KeyRegistrationFunctionality =
  record
    { State = ⊤
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    }

open import Leios.Base d-Abstract d-VRF

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

open import Leios.FFD

instance
  isb : IsBlock (List ⊤)
  isb =
    record
      { slotNumber = λ _ → 0
      ; producerID = λ _ → 1
      ; lotteryPf = λ _ → tt
      }

  hhs : ∀ {b} → Hashable (IBHeaderOSig b) ⊤
  hhs = record { hash = λ _ → tt }

  hpe : Hashable PreEndorserBlock ⊤
  hpe = record { hash = λ x → tt }

d-FFDFunctionality : FFDAbstract.Functionality ffdAbstract
d-FFDFunctionality =
  record
    { State = ⊤
    ; initFFDState = tt
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    ; FFD-total = tt , tt
    }

open import Leios.Voting
open import Data.Fin using (Fin)

d-VotingAbstract : VotingAbstract (Fin 1 × EndorserBlock)
d-VotingAbstract =
  record
    { VotingState = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

st : SpecStructure 1
st = record
      { a = d-Abstract
      ; id = 1
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

open SpecStructure st

open import Leios.Short st

open Protocol

s₀ : LeiosState
s₀ = initLeiosState tt (singletonᵐ 1 1) tt

open import Leios.Traces st _-⟦_/_⟧⇀_

-- i) Same slot

ftch-step : s₀ ⇉ s₀
ftch-step = (FTCH-LDG , FTCH-LDG []) , Ftch

trace : s₀ ⇉⋆ s₀
trace = 1 , (s₀ , (ftch-step , refl))

-- ii) Slot transition

t₁ : LeiosState
t₁ = addUpkeep s₀ IB-Role

t₂ : LeiosState
t₂ = addUpkeep t₁ EB-Role

t₃ : LeiosState
t₃ = addUpkeep t₂ V-Role

t₄ : LeiosState
t₄ = addUpkeep t₃ Base

s₁ : LeiosState
s₁ = let open LeiosState t₄ in
  record t₄
    { FFDState = tt
    ; BaseState = tt
    ; Ledger = []
    ; IBs = []
    ; IBHeaders = []
    ; IBBodies = []
    ; EBs = []
    ; Vs = []
    ; slot = suc slot
    ; Upkeep = ∅
    }

stake≡1 : stake s₀ ≡ 1
stake≡1 = {!!}

ib-step : s₀ ⇉ t₁
ib-step = (SLOT , EMPTY) , Roles (IB-Role {π = tt} uk π-IB tt)
  where
    uk : IB-Role ∉ LeiosState.Upkeep s₀
    uk = λ x → ∉-∅ x

    π-IB : canProduceIB (LeiosState.slot s₀) tt (stake s₀) tt
    π-IB rewrite stake≡1 = s≤s z≤n , refl

open Equivalence

open import Function.Related.TypeIsomorphisms
import Data.Sum

lem1 : ∀ {A} {a : A} {B C : ℙ A} → a ∉ B → a ∉ C → a ∉ B ∪ C
lem1 {_} {_} {B} {C} x y = Data.Sum.[ x , y ] ∘ ∈-∪⁻ {X = B} {Y = C}

lem2 : ∀ {A} {a : A} {B : ℙ A} → a ∉ B → a ∉ ∅ ∪ B
lem2 {_} {_} {B} = lem1 {B = ∅} {C = B} ∉-∅

lem3 : ∀ {A} {a b : A} → a ≢ b → a ∉ singleton b
lem3 = to (¬-cong-⇔ ∈-singleton)

eb-step : t₁ ⇉ t₂
eb-step = (SLOT , EMPTY) , Roles (EB-Role {π = tt} uk π-EB tt)
  where
    uk : EB-Role ∉ ∅ ∪ ❴ IB-Role ❵
    uk = lem2 (lem3 (λ ()))

    π-EB : canProduceEB (LeiosState.slot s₀) tt (stake s₀) tt
    π-EB rewrite stake≡1 = s≤s z≤n , refl

v-step : t₂ ⇉ t₃
v-step = (SLOT , EMPTY) , Roles (V-Role uk π-V tt)
  where
    uk : V-Role ∉ (∅ ∪ ❴ IB-Role ❵) ∪ ❴ EB-Role ❵
    uk = lem1 (lem2 (lem3 λ ())) (lem3 λ ())

    π-V : canProduceV (LeiosState.slot s₀) tt (stake s₀)
    π-V rewrite stake≡1 = s≤s z≤n

base-step : t₃ ⇉ t₄
base-step = (SLOT , EMPTY) , Base₂b uk refl tt
  where
    uk : Base ∉ ((∅ ∪ ❴ IB-Role ❵) ∪ ❴ EB-Role ❵) ∪ ❴ V-Role ❵
    uk = lem1 (lem1 (lem2 (lem3 λ ())) (lem3 λ ())) (lem3 λ ())

slot-step : t₄ ⇉ s₁
slot-step = (SLOT , EMPTY) , Slot {rbs = []} {msgs = []} uk tt tt
  where
    uk : (((∅ ∪ ❴ IB-Role ❵) ∪ ❴ EB-Role ❵) ∪ ❴ V-Role ❵) ∪ ❴ Base ❵ ≡ᵉ allUpkeep
    uk = {!!}

slot-transition-trace : s₀ ⇉⋆ s₁
slot-transition-trace = 5
  , t₁ , ib-step
  , t₂ , eb-step
  , t₃ , v-step
  , t₄ , base-step
  , s₁ , slot-step
  , refl
