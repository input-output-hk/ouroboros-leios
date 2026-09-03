{- Module: Defaults

   Concrete instantiation of the Leios 'SpecStructure' obligations used by the
   trace verifier. It mirrors the spec's own 'Test.Defaults' (so the verifier
   does not depend on a testing module), with one deliberate difference: voting
   (VT) eligibility follows the deterministic, epoch-fixed committee of CIP-0164
   computed from the stake distribution, whereas block production (EB) is
   decided by the 'winning-slots' oracle (the Praos VRF leadership schedule)
   supplied through 'TestParams'. See 'sortition' below.

   The cryptographic components stay abstract: hashing is the identity on the
   relevant payloads, signatures/proofs are the unit type. The base layer is
   the real Praos node from ouroboros-praos-formal-spec, wrapped as a
   BaseMachine by Leios.Base.Praos (see d-BaseFunctionality below and
   docs/praos-base-machine-sketch.md).

   Not '--safe' (it was, with the previous stub base machine): the Praos
   instantiation transitively imports Protocol.Chain, whose chainFromBlock is
   TERMINATING. The block-tree laws themselves are proved, not postulated
   (Leios.Base.Praos.Assumptions).
-}

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.Config
open import Leios.SpecStructure

open import Axiom.Set.Properties th
open import Data.Bool using (if_then_else_)
open import Data.Nat.Show as N
import Data.Nat as Nat
open import Data.Fin.Base using (toℕ)
open import Data.Integer hiding (_≟_)
open import Data.String as S using (intersperse)
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.Structures

open import Tactic.Defaults
open import Tactic.Derive.DecEq

open import LibExt

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

-- Base layer: the real Praos node (ouroboros-praos-formal-spec, wrapped by
-- Leios.Base.Praos — see docs/praos-base-machine-sketch.md). Cert/VTy/
-- initSlot/V-chkCerts keep the trivial choices the previous stub machine
-- made, so the verifier-facing BaseIOF interface is unchanged; what changes
-- is the machine behind it: FTCH-LDG/FTCH-SLOT answers and RB minting now
-- follow Praos's honest-node semantics (processMsgsʰ/makeBlockʰ/bestChain)
-- instead of echoing untouched state.

-- RB-production eligibility for the wrapped Praos node: the same
-- leadership-schedule oracle 'sortition' consults under the EB tag (in
-- linear Leios the RB is the Praos block; a leader slot lets the SUT mint an
-- RB, announcing an EB in it). The party argument is deliberately ignored:
-- the schedule is the SUT's own and the machine only ever evaluates 'winner'
-- at its own identity (makeBlockʰ), which also neutralizes the
-- party₀-vs-sutId identity fixed inside Leios.Base.Praos.Assumptions.
-- Slot 0 is a universal winner: it discharges the Praos Assumptions record's
-- genesisWinner (only the genesis block sits at slot 0) and changes no real
-- behavior — the machine never mints at slot 0 (Deliver mints at `suc
-- clock`), so the schedule is only ever consulted at slots ≥ 1.
d-winner : Fin numberOfParties → ℕ → Type
d-winner _ Nat.zero     = ⊤
d-winner _ (Nat.suc sl) = (EB , Nat.suc sl) ∈ winning-slots

-- Deliberately NOT an instance: `d-winner _ zero` reduces to ⊤, so as an
-- instance this would overlap with Dec-⊤ in unrelated searches. It is passed
-- to the Praos machine explicitly below.
d-winner⁇² : d-winner ⁇²
d-winner⁇² {_} {Nat.zero}   .dec = yes tt
d-winner⁇² {_} {Nat.suc sl} .dec = (EB , Nat.suc sl) ∈? winning-slots

-- Block-content hash for the Praos tree's prev-linkage: slot and producer
-- uniquely identify honest blocks; the payload part disambiguates the rest.
d-blockHash : ℕ → Fin numberOfParties → RankingBlock → List ℕ
d-blockHash sl pid rb =
  sl ∷ toℕ pid ∷ RankingBlock.slot rb ∷ maybe (λ x → x) [] (RankingBlock.announcedEB rb)

import Leios.Base.Praos.Machine as PraosMachine
module PM = PraosMachine d-Abstract d-VRF numberOfParties d-winner
  ⦃ winner⁇² = λ {p} {sl} → d-winner⁇² {p} {sl} ⦄
  (λ _ → tt)
  d-blockHash
-- producer is a placeholder (a bare RankingBlock does not determine its
-- minter) but operationally inert: IsBlockchain's producer/slotOf are read
-- only by deployment-level modules the verifier never imports.
module PB = PM.Assembled ⊤ ⊤ (λ _ → 0) (λ _ _ → true) stakeDistribution (λ _ → sutId)

d-Base : BaseAbstract
d-Base = PB.B'

d-BaseFunctionality : BaseAbstract.BaseMachine d-Base
d-BaseFunctionality = PB.praosBase

-- The Praos node's honest-local interface (tree state, block insertion,
-- chain read-out) plus block construction/hashing, for the verifier to
-- maintain the SUT's block tree from trace events.
open PM public using (mkPraosBlock; praosBlockHash; genesisHash)

open import Leios.Base.Praos d-Abstract d-VRF using (PraosAbstract)
module PraosNode = PraosAbstract PM.praosNode

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

  -- Votes sign the announcing RB's hash: slot plus announced-EB payload.
  hrb : Hashable RankingBlock Hash
  hrb .hash rb = RankingBlock.slot rb ∷ maybe (λ x → x) [] (RankingBlock.announcedEB rb)

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
      ; Hashable-RankingBlock     = hrb
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
