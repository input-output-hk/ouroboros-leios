{- Module: Defaults

   Concrete instantiation of the Leios 'SpecStructure' obligations used by the
   trace verifier. Previously the verifier borrowed these from the spec's
   testing module 'Test.Defaults'; they are provided here directly so the
   verifier does not depend on a testing module.

   The Leios specification keeps the cryptographic components abstract (it is
   '--safe', so there is no real VRF/signature/hashing), hence these instances
   are the canonical concrete choices: hashing is the identity on the relevant
   payloads, signatures/proofs are the unit type, and eligibility ('sortition')
   is split by role -- block production (EB) is decided by the 'winning-slots'
   oracle (the Praos VRF leadership schedule) supplied through 'TestParams',
   whereas voting (VT) follows the deterministic, epoch-fixed committee of
   CIP-0164 computed from the stake distribution. The base layer, key
   registration, FFD and voting functionalities are the minimal implementations
   the small-step relation needs.
-}

open import Leios.Prelude
open import Leios.Abstract
open import Leios.Config
open import Leios.SpecStructure

open import Axiom.Set.Properties th
open import Data.Bool using (if_then_else_)
open import Data.Nat.Show as N
import Data.Nat as Nat
open import Data.Integer hiding (_≟_)
open import Data.String as S using (intersperse)
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Structures

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open Equivalence

module Defaults
  (params : Params) (let open Params params)
  (testParams : TestParams params) (let open TestParams testParams) where

instance
  htx : Hashable (List ℕ) (List ℕ)
  htx = record { hash = id }

d-Abstract : LeiosAbstract
d-Abstract =
  record
    { Tx                = ℕ
    ; PoolID            = Fin numberOfParties
    ; BodyHash          = List ℕ
    ; VrfPf             = ⊤
    ; PrivKey           = BlockType × ⊤
    ; Sig               = ⊤
    ; Hash              = List ℕ
    ; EBCert            = List ℕ
    ; getEBHash         = id
    ; Vote              = ⊤
    ; vote              = λ _ _ → tt
    ; sign              = λ _ _ → tt
    }

open LeiosAbstract d-Abstract public

open import Leios.VRF d-Abstract public

sutStake : ℕ
sutStake = TotalMap.lookup stakeDistribution sutId

-- Voting-committee selection (CIP-0164).
--
-- The Leios voting committee is NOT a per-slot VRF lottery.  It is fixed once
-- per epoch, deterministically, from the epoch-boundary stake distribution:
-- order pools by active stake (descending) and accumulate stake until the
-- cumulative coverage reaches the target σc (equivalently, until the
-- truncation error falls below εc = 1 − σc).  That prefix is the committee;
-- every member may vote on every EB of the epoch.
--
-- We fix σc = 99/100 (99% cumulative active-stake coverage), expressed as a
-- rational σc-num / σc-den so the threshold test stays all-naturals (--safe,
-- no floats).
σc-num σc-den : ℕ
σc-num = 99
σc-den = 100

-- Stake of every party, paired with its index.
partyStakes : List (Fin numberOfParties × ℕ)
partyStakes = tabulate (λ i → i , TotalMap.lookup stakeDistribution i)

totalStake : ℕ
totalStake = foldr (λ (_ , s) acc → s Nat.+ acc) 0 partyStakes

-- Stake of a pool that strictly precedes the SUT in committee order, else 0.
-- Order is descending stake, ties broken by ascending index (deterministic),
-- so a pool precedes the SUT iff it has more stake, or equal stake and a
-- smaller index.
precedingContribution : Fin numberOfParties → ℕ → ℕ
precedingContribution i s =
  if sutStake Nat.<ᵇ s then s
  else if s Nat.<ᵇ sutStake then 0
  else if toℕ i Nat.<ᵇ toℕ sutId then s
  else 0

-- Cumulative stake of all pools ahead of the SUT in committee order.
precedingStake : ℕ
precedingStake =
  foldr (λ (i , s) acc → precedingContribution i s Nat.+ acc) 0 partyStakes

-- The SUT is on the committee iff the pools ahead of it have not yet covered
-- the target σc, i.e. precedingStake < σc · totalStake (in all-naturals form,
-- precedingStake · σc-den < totalStake · σc-num).
sut-in-committee : Bool
sut-in-committee = (precedingStake Nat.* σc-den) Nat.<ᵇ (totalStake Nat.* σc-num)

-- Eligibility.  Block production (EB) follows the Praos VRF leadership schedule
-- supplied through the 'winning-slots' oracle.  Voting (VT) follows the
-- deterministic committee above and is independent of the slot.
sortition : BlockType → ℕ → ℕ
sortition VT _ = if sut-in-committee then 0 else sutStake
sortition b n with (b , n) ∈? winning-slots
... | yes _ = 0
... | no _ = sutStake

d-VRF : LeiosVRF
d-VRF =
  record
    { PubKey     = Fin numberOfParties × ⊤
    ; vrf        =
        record
          { isKeyPair = λ _ _ → ⊤
          ; eval      = λ (b , _) y → sortition b y , tt
          ; verify    = λ _ _ _ _ → ⊤
          ; verify?   = λ _ _ _ _ → yes tt
          }
    ; genIBInput = id
    ; genEBInput = id
    ; genVInput  = id
    ; genV1Input = id
    ; genV2Input = id
    ; poolID     = proj₁
    ; verifySig  = λ _ _ → ⊤
    ; verifySig? = λ _ _ → yes tt
    }

open LeiosVRF d-VRF public

open import Leios.Blocks d-Abstract public
open import Leios.KeyRegistration d-Abstract d-VRF public

d-KeyRegistration : KeyRegistrationAbstract
d-KeyRegistration = _

d-KeyRegistrationFunctionality : KeyRegistrationAbstract.Functionality d-KeyRegistration
d-KeyRegistrationFunctionality =
  record
    { State     = ⊤
    ; _-⟦_/_⟧⇀_ = λ _ _ _ _ → ⊤
    }

open import Leios.Base d-Abstract d-VRF public

d-Base : BaseAbstract
d-Base =
  record
    { Cert       = ⊤
    ; VTy        = ⊤
    ; initSlot   = λ _ → 0
    ; V-chkCerts = λ _ _ → true
    }

d-BaseFunctionality : BaseAbstract.Functionality d-Base
d-BaseFunctionality =
  record
    { State         = ⊤
    ; _-⟦_/_⟧⇀_     = λ _ _ _ _ → ⊤
    ; SUBMIT-total  = tt , tt
    ; FTCH-total    = [] , tt , tt
    }

open import Leios.FFD public

instance
  isb : IsBlock (List Vote)
  isb =
    record
      { slotNumber = λ _ → 0
      ; producerID = λ _ → sutId
      ; lotteryPf  = λ _ → tt
      }

  hpe : Hashable PreEndorserBlock Hash
  hpe .hash = EndorserBlockOSig.txs

record FFDBuffers : Type where
  field inEBs : List EndorserBlock
        inVTs : List (List Vote)

        outEBs : List EndorserBlock
        outVTs : List (List Vote)

unquoteDecl DecEq-FFDBuffers = derive-DecEq ((quote FFDBuffers , DecEq-FFDBuffers) ∷ [])

open GenFFD.Header
open FFDBuffers

flushIns : FFDBuffers → List (GenFFD.Header ⊎ GenFFD.Body)
flushIns record { inEBs = ebs ; inVTs = vts } =
  L.map (inj₁ ∘ ebHeader) ebs ++ L.map (inj₁ ∘ vtHeader) vts


data SimpleFFD : FFDBuffers → FFDAbstract.Input ffdAbstract → FFDAbstract.Output ffdAbstract → FFDBuffers → Type where
  SendEB : ∀ {s eb}     → SimpleFFD s (FFDAbstract.Send (ebHeader eb) nothing) FFDAbstract.SendRes (record s { outEBs = eb ∷ outEBs s})
  SendVS : ∀ {s vs}     → SimpleFFD s (FFDAbstract.Send (vtHeader vs) nothing) FFDAbstract.SendRes (record s { outVTs = vs ∷ outVTs s})

  BadSendEB : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (ebHeader h) (just b)) FFDAbstract.SendRes s
  BadSendVS : ∀ {s h b} → SimpleFFD s (FFDAbstract.Send (vtHeader h) (just b)) FFDAbstract.SendRes s

  Fetch : ∀ {s}         → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes (flushIns s)) (record s { inEBs = [] ; inVTs = [] })

send-total : ∀ {s h b} → ∃[ s' ] (SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s')
send-total {s} {ebHeader eb} {nothing}        = record s { outEBs = eb ∷ outEBs s} , SendEB
send-total {s} {vtHeader vs} {nothing}        = record s { outVTs = vs ∷ outVTs s} , SendVS

send-total {s} {ebHeader eb} {just _} = s , BadSendEB
send-total {s} {vtHeader vs} {just _} = s , BadSendVS

fetch-total : ∀ {s} → ∃[ x ] (∃[ s' ] (SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes x) s'))
fetch-total {s} = flushIns s , (record s { inEBs = [] ; inVTs = [] } , Fetch)

send-complete : ∀ {s h b s'} → SimpleFFD s (FFDAbstract.Send h b) FFDAbstract.SendRes s' → s' ≡ proj₁ (send-total {s} {h} {b})
send-complete SendEB    = refl
send-complete SendVS    = refl
send-complete BadSendEB = refl
send-complete BadSendVS = refl

fetch-complete₁ : ∀ {s r s'} → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes r) s' → s' ≡ proj₁ (proj₂ (fetch-total {s}))
fetch-complete₁ Fetch = refl

fetch-complete₂ : ∀ {s r s'} → SimpleFFD s FFDAbstract.Fetch (FFDAbstract.FetchRes r) s' → r ≡ proj₁ (fetch-total {s})
fetch-complete₂ Fetch = refl

instance
  Dec-SimpleFFD : ∀ {s i o s'} → SimpleFFD s i o s' ⁇
  Dec-SimpleFFD {s} {FFDAbstract.Send h b} {FFDAbstract.SendRes} {s'} with s' ≟ proj₁ (send-total {s} {h} {b})
  ... | yes p rewrite p = ⁇ yes (proj₂ send-total)
  ... | no ¬p = ⁇ no λ x → ⊥-elim (¬p (send-complete x))
  Dec-SimpleFFD {_} {FFDAbstract.Send _ _} {FFDAbstract.FetchRes _} {_} = ⁇ no λ ()
  Dec-SimpleFFD {s} {FFDAbstract.Fetch} {FFDAbstract.FetchRes r} {s'}
    with s' ≟ proj₁ (proj₂ (fetch-total {s})) | r ≟ proj₁ (fetch-total {s}) -- TODO: improve performance
  ... | yes p | yes q rewrite p rewrite q = ⁇ yes (proj₂ (proj₂ (fetch-total {s})))
  ... | _     | no ¬q = ⁇ no λ x → ⊥-elim (¬q (fetch-complete₂ x))
  ... | no ¬p | _     = ⁇ no λ x → ⊥-elim (¬p (fetch-complete₁ x))
  Dec-SimpleFFD {_} {FFDAbstract.Fetch} {FFDAbstract.SendRes} {_} = ⁇ no λ ()

d-FFDFunctionality : FFDAbstract.Functionality ffdAbstract
d-FFDFunctionality =
  record
    { State         = FFDBuffers
    ; initFFDState  = record { inEBs = []; inVTs = []; outEBs = []; outVTs = [] }
    ; _-⟦_/_⟧⇀_     = SimpleFFD
    }

open import Leios.Voting public

d-VotingAbstract : VotingAbstract EndorserBlock
d-VotingAbstract =
  record
    { VotingState     = ⊤
    ; initVotingState = tt
    ; isVoteCertified = λ _ _ → ⊤
    }

d-SpecStructure : SpecStructure
d-SpecStructure = record
      { a                         = d-Abstract
      ; Hashable-PreEndorserBlock = hpe
      ; id                        = sutId
      ; FFD'                      = d-FFDFunctionality
      ; vrf'                      = d-VRF
      ; sk-EB                     = EB , tt
      ; sk-VT                     = VT , tt
      ; pk-EB                     = sutId , tt
      ; pk-VT                     = sutId , tt
      ; B'                        = d-Base
      ; BF                        = d-BaseFunctionality
      ; initBaseState             = tt
      ; K'                        = d-KeyRegistration
      ; KF                        = d-KeyRegistrationFunctionality
      ; va                        = d-VotingAbstract
      ; getEBCert                 = λ _ → []
      }
