{-# OPTIONS --safe #-}
{- Module: Defaults

   Concrete instantiation of the Leios 'SpecStructure' obligations used by the
   trace verifier. It mirrors the spec's own 'Test.Defaults' (so the verifier
   does not depend on a testing module), with one deliberate difference: voting
   (VT) eligibility follows the deterministic, epoch-fixed committee of CIP-0164
   computed from the stake distribution, whereas block production (EB) is
   decided by the 'winning-slots' oracle (the Praos VRF leadership schedule)
   supplied through 'TestParams'. See 'sortition' below.

   The cryptographic components stay abstract (this is '--safe'): hashing is the
   identity on the relevant payloads, signatures/proofs are the unit type. The
   base layer is the spec's simple single-producer blockchain machine.
-}

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.Config
open import Leios.SpecStructure
open import Blockchain.Safety
import Blockchain.IsBlockchain

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

open import LibExt

open import CategoricalCrypto using (I ; Machine ; machine-type ; Channel ; _⊗ᵀ_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection

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
    ; splitTxs          = λ l → [] , l
    }

open LeiosAbstract d-Abstract public

open import Leios.VRF d-Abstract public

sutStake : ℕ
sutStake = TotalMap.lookup stakeDistribution sutId

-- Eligibility for block production (EB): the Praos VRF leadership schedule
-- supplied through the 'winning-slots' oracle. Voting (VT) eligibility does
-- not go through the VRF at all: it is the explicit CIP-0164 stake-truncation
-- committee, `inVotingCommittee` in Leios.Config.
sortition : BlockType → ℕ → ℕ
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
    { Cert        = ⊤
    ; VTy         = ⊤
    ; initSlot    = λ _ → 0
    ; V-chkCerts  = λ _ _ → true
    ; BaseAdv     = I
    ; BaseMsg     = ⊤
    }

d-BaseState : Type
d-BaseState = List RankingBlock × ℕ

d-BaseChannel : Channel
d-BaseChannel = BaseNetwork ⊗ᵀ (BaseIO ⊗₀ BaseAdv)
  where open BaseAbstract d-Base

data d-BaseRel : machine-type d-BaseState d-BaseChannel where

  fetch-blocks :
    ∀ blocks slot →
      d-BaseRel
        (blocks , slot)
        (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ BaseAbstract.FTCH-LDG)
        (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.BASE-LDG blocks))
        (blocks , slot)

  fetch-slot :
    ∀ blocks slot →
      d-BaseRel
        (blocks , slot)
        (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ BaseAbstract.FTCH-SLOT)
        (just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.SLOT slot))
        (blocks , slot)

open Blockchain.IsBlockchain (Fin 1)

helper : BlockChainInfo RankingBlock → BaseAbstract.BaseIOF d-Base CategoricalCrypto.Out
helper = let open BaseAbstract.BaseIOF in λ where
  Chain → FTCH-LDG
  Slot  → FTCH-SLOT

private
  open BaseAbstract.BaseIOF

  opaque
    unfolding _⊗₀_

    correctness-chain : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG) response' s'
      → ∃ λ response → response' ≡ just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BASE-LDG response)
    correctness-chain (fetch-blocks blocks _) = blocks , refl

    correctness-slot : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-SLOT) response' s'
      → ∃ λ response → response' ≡ just (L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ SLOT response)
    correctness-slot (fetch-slot _ slot) = slot , refl

    isPure-chain : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-LDG) response' s'
      → s ≡ s'
    isPure-chain (fetch-blocks _ _) = refl

    isPure-slot : ∀ {s response' s'}
      → d-BaseRel s (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ FTCH-SLOT) response' s'
      → s ≡ s'
    isPure-slot (fetch-slot _ _) = refl

d-BaseFunctionality : BaseAbstract.BaseMachine d-Base
d-BaseFunctionality =
  record
    { n = 1
    ; m =
        record
          { State = (List RankingBlock × ℕ)
          ; stepRel = d-BaseRel
          }
    ; is-blockchain = let open BaseAbstract.BaseIOF in
        record
          { isConstrained =
              record
                { queryI = (L⊗ (ϵ ⊗R) ᵗ¹ ↑ₒ_) ∘ helper
                ; queryO = λ where
                    {Chain} rankingBlocks → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BASE-LDG rankingBlocks
                    {Slot}  slot          → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ SLOT slot
                ; correctness = λ where
                    {Chain} → correctness-chain
                    {Slot}  → correctness-slot
                ; completeness = λ where
                    {Chain} {blocks , slot} → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.BASE-LDG blocks , (blocks , slot) , fetch-blocks blocks slot
                    {Slot}  {blocks , slot} → L⊗ (ϵ ⊗R) ᵗ¹ ↑ᵢ BaseAbstract.SLOT     slot   , (blocks , slot) , fetch-slot   blocks slot
                }
          ; isPure = λ where
              Chain → isPure-chain
              Slot  → isPure-slot
          ; producer = λ _ → Fin.zero
          ; slotOf   = λ _ → 0
          }
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
      ; BM                        = d-BaseFunctionality
      ; K'                        = d-KeyRegistration
      ; KF                        = d-KeyRegistrationFunctionality
      ; va                        = d-VotingAbstract
      ; getEBCert                 = λ _ → []
      -- The verifier cannot observe validation completion from the trace; the
      -- node's own gate ensures it only votes after validating, so a logged
      -- vote is taken as evidence of completed validation. To be refined via
      -- the asynchronous Validation functionality (see the
      -- yveshauser/validation-functionality spec branch).
      ; isValidityChecked         = λ _ _ → ⊤
      ; isValidityChecked?        = λ _ _ → yes tt
      }
