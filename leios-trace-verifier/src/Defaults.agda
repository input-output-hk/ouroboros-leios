{- Module: Defaults

   Concrete instantiation of the Leios 'SpecStructure' obligations used by the
   trace verifier. It mirrors the spec's own 'Test.Defaults' (so the verifier
   does not depend on a testing module), with one deliberate difference: voting
   (VT) eligibility follows the voting committee of the Dijkstra-era ledger
   specification, selected from the stake distribution
   ('Leios.Ledger.Dijkstra.Verifier'), whereas block production (EB) is
   decided by the 'winning-slots' oracle (the Praos VRF leadership schedule)
   supplied through 'TestParams'. See 'sortition' below.  The slots in which
   the SUT mints a ranking block, 'rb-slots', are a separate parameter: a
   leader may put the transactions in the ranking block and announce no EB,
   so these slots carry no EB obligation.  See 'd-winner' below.

   The types of the abstract interface are the Dijkstra-era ledger
   specification's ('Leios.Ledger.Dijkstra', at 'Leios.Ledger.Dijkstra.Verifier.verifierGov'):
   a transaction is a reference (hash, declared size), an EB is identified by
   its references, EB identifiers and ranking-block hashes are kept apart
   ('Hash = EBHash ⊎ RBHeaderHash'), and a certificate is the ledger's,
   tagged with the ranking block it certifies.  The traces record transaction
   ids but no sizes, and certificates but no signers, so sizes are 0 and
   certificates unsigned ('txRef', 'certFor').

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

import Data.Nat as Nat
open import Data.Fin.Base using (toℕ)

open import Tactic.Defaults
open import Tactic.Derive.DecEq

module Defaults
  (params : Params) (let open Params params)
  (testParams : TestParams params) (let open TestParams testParams)
  -- The slots in which the SUT leads, and mints a ranking block.
  (rb-slots : ℙ ℕ)
  -- The ledger's committee size ('leiosCommitteeSize').
  (committeeSize : ℕ)
  where

import Leios.Ledger.Dijkstra.Verifier as LV
import Leios.Ledger.Dijkstra LV.verifierGov as LD

-- What the Leios protocol needs and the ledger does not provide.  Voting
-- keys are the party's, the SUT is the only voter.
d-OffLedger : LD.OffLedger
d-OffLedger =
  record
    { n         = numberOfParties
    ; keyOf     = LV.keyOf
    ; LVrfPf    = ⊤
    ; LPrivKey  = BlockType × ⊤
    ; LSig      = ⊤
    ; LBodyHash = List ℕ
    ; voterOf   = λ _ → sutId
    ; lsign     = λ _ _ → tt
    ; lsplitTxs = λ l → [] , l
    }

d-Abstract : LeiosAbstract
d-Abstract = LD.dijkstraAbstract d-OffLedger

open LeiosAbstract d-Abstract public

-- A transaction as a trace records it: its id, with no declared size.
txRef : ℕ → Tx
txRef t = t , 0

-- A ranking-block hash.
rbRef : List ℕ → Hash
rbRef = inj₂

-- The hash's payload, whichever kind it is.
hashList : Hash → List ℕ
hashList = [ id , id ]′

-- The certificate for the ranking block with this hash, as a trace records it.
certFor : List ℕ → EBCert
certFor r = LD.⟨ r , LV.unsignedCert ⟩ᶜ

instance
  Show-Hash : Show Hash
  Show-Hash .show (inj₁ h) = "EB " ◇ show ⦃ Show-List ⦄ h
  Show-Hash .show (inj₂ h) = "RB " ◇ show ⦃ Show-List ⦄ h

  Show-Cert : Show EBCert
  Show-Cert .show c = "Cert " ◇ show ⦃ Show-List ⦄ (LD.certRef c)

open import Leios.VRF d-Abstract public

sutStake : ℕ
sutStake = TotalMap.lookup stakeDistribution sutId

-- Eligibility for block production (EB): the Praos VRF leadership schedule
-- supplied through the 'winning-slots' oracle. Voting (VT) eligibility does
-- not go through the VRF at all: it is the ledger's committee ('inCommittee'
-- below).
sortition : ℕ → ℕ
sortition n with n ∈? winning-slots
... | yes _ = 0
... | no _ = sutStake

d-VRF : LeiosVRF
d-VRF =
  record
    { PubKey     = Fin numberOfParties × ⊤
    ; vrf        =
        record
          { isKeyPair = λ _ _ → ⊤
          ; eval      = λ _ y → sortition y , tt
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

-- RB-production eligibility for the wrapped Praos node: for the SUT, the
-- slots 'rb-slots' (in linear Leios the RB is the Praos block; a leader slot
-- lets the SUT mint an RB, which may announce an EB).  The schedules of the other parties are unknown, so their blocks are
-- taken as the log has them: every slot is theirs to win.  Without this, a
-- block of another party would only be valid in a winning slot of the SUT,
-- and the node would never extend it.
-- Slot 0 is a universal winner: it discharges the Praos Assumptions record's
-- genesisWinner (only the genesis block sits at slot 0) and changes no real
-- behavior — the machine never mints at slot 0 (Deliver mints at `suc
-- clock`), so the schedule is only ever consulted at slots ≥ 1.
d-winner : Fin numberOfParties → ℕ → Type
d-winner _ Nat.zero     = ⊤
d-winner p (Nat.suc sl) = p ≡ sutId → Nat.suc sl ∈ rb-slots

-- Deliberately NOT an instance: `d-winner _ zero` reduces to ⊤, so as an
-- instance this would overlap with Dec-⊤ in unrelated searches. It is passed
-- to the Praos machine explicitly below.
d-winner⁇² : d-winner ⁇²
d-winner⁇² {_} {Nat.zero}   .dec = yes tt
d-winner⁇² {p} {Nat.suc sl} .dec with p ≟ sutId | Nat.suc sl ∈? rb-slots
... | no p≢  | _       = yes λ p≡ → ⊥-elim (p≢ p≡)
... | yes _  | yes w   = yes λ _ → w
... | yes p≡ | no ¬w   = no λ f → ¬w (f p≡)

-- Block hash for the Praos tree's prev-linkage: slot and producer, which
-- identify honest blocks.  The payload is left out: the node mints the SUT's
-- blocks with the payload Leios submitted, which the log does not record,
-- while the blocks of other parties name them as parents by their log id.
-- Two blocks of one producer in one slot (equivocation) are not told apart.
d-blockHash : ℕ → Fin numberOfParties → RankingBlock → Hash
d-blockHash sl pid _ = rbRef (sl ∷ toℕ pid ∷ [])

import Leios.Base.Praos.Machine as PraosMachine
module PM = PraosMachine d-Abstract d-VRF numberOfParties d-winner
  ⦃ winner⁇² = λ {p} {sl} → d-winner⁇² {p} {sl} ⦄
  (λ _ → tt)
  d-blockHash
  sutId
-- producer and slotOf are placeholders (a bare RankingBlock determines
-- neither its minter nor its slot) but operationally inert: IsBlockchain's
-- producer/slotOf are read only by deployment-level modules the verifier
-- never imports.
module PB = PM.Assembled ⊤ ⊤ (λ _ → 0) (λ _ _ → true) stakeDistribution (λ _ → sutId) (λ _ → 0)

d-Base : BaseAbstract
d-Base = PB.B'

d-BaseFunctionality : BaseAbstract.BaseMachine d-Base
d-BaseFunctionality = PB.praosBase

-- The same node without its (empty) adversary port, for stacking Linear
-- Leios on it (LinearLeiosStack), and its trace checker 'Check'.  A verifier
-- picks what its log observes: blocks by parent and slot ('praosHeader'),
-- which is what a log records of the blocks the node mints (their payload is
-- Leios's, see 'd-blockHash'), and the selected chain by its tip
-- ('tipHash'), where the log names it.
open PB public using (node⁻; NodeState; initNodeState; module Check)
open PM public using (praosHeader)

-- The Praos node's honest-local interface (tree state, block insertion,
-- chain read-out) plus block construction/hashing, for the verifier to
-- maintain the SUT's block tree from trace events.
open PM public using (mkPraosBlock; praosBlockHash; genesisHash)

open import Leios.Base.Praos d-Abstract d-VRF using (PraosAbstract)
module PraosNode = PraosAbstract PM.praosNode

-- The hash of the tip of a selected chain, which a node log names.
tipHash : List PraosNode.Block → Hash
tipHash []      = PM.genesisHash
tipHash (b ∷ _) = PM.praosBlockHash b

open import Leios.FFD public

instance
  isb : IsBlock (List Vote)
  isb =
    record
      { slotNumber = λ _ → 0
      ; producerID = λ _ → sutId
      ; lotteryPf  = λ _ → tt
      }

  -- The ledger's EB identifier: the EB's references ('hashEB').
  hpe : Hashable PreEndorserBlock Hash
  hpe = LD.Hashable-PreEndorserBlock d-OffLedger

  -- Votes sign the announcing RB's hash: body payload plus announced-EB hash.
  hrb : Hashable RankingBlock Hash
  hrb .hash rb = let open RankingBlock rb in
    rbRef ([ L.map proj₁ , LD.certRef ]′ txsOrEbCert ++ maybe hashList [] announcedEB)

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
  ... | no ¬p = ⁇ no (¬p ∘ send-complete)
  Dec-SimpleFFD {_} {FFDAbstract.Send _ _} {FFDAbstract.FetchRes _} {_} = ⁇ no λ ()
  Dec-SimpleFFD {s} {FFDAbstract.Fetch} {FFDAbstract.FetchRes r} {s'}
    with s' ≟ proj₁ (proj₂ (fetch-total {s})) | r ≟ proj₁ (fetch-total {s}) -- TODO: improve performance
  ... | yes p | yes q rewrite p rewrite q = ⁇ yes (proj₂ (proj₂ (fetch-total {s})))
  ... | _     | no ¬q = ⁇ no (¬q ∘ fetch-complete₂)
  ... | no ¬p | _     = ⁇ no (¬p ∘ fetch-complete₁)
  Dec-SimpleFFD {_} {FFDAbstract.Fetch} {FFDAbstract.SendRes} {_} = ⁇ no λ ()

d-FFDFunctionality : FFDAbstract.Functionality ffdAbstract
d-FFDFunctionality =
  record
    { State         = FFDBuffers
    ; initFFDState  = record { inEBs = []; inVTs = []; outEBs = []; outVTs = [] }
    ; _-⟦_/_⟧⇀_     = SimpleFFD
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
      -- The pinned spec's vote rule asks this static oracle, which cannot
      -- read the state of a validation functionality.  The verifier runs the
      -- validation machine (Leios.Ledger.Validation) beside Linear Leios
      -- instead, and checks the EB of every vote against it there (see
      -- LinearLeiosStack); here every EB counts as validated.
      ; isValidityChecked         = λ _ _ → ⊤
      ; isValidityChecked?        = λ _ _ → yes tt
      -- The ledger's committee, for the stake distribution in force.
      ; inCommittee               = λ sd p → LV.inCommittee sd committeeSize p
      ; inCommittee?              = λ sd p → LV.inCommittee? sd committeeSize p
      }
