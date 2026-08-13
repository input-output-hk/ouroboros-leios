-- A concrete Assumptions instance for Leios.Base.Praos.Instance, closing the
-- module parameter that docs/praos-base-machine-sketch.md flagged as
-- missing: "no concrete Tree implementation with discharged laws exists
-- upstream, so it stays a parameter."
--
-- The TreeImpl (a plain pool of delivered blocks) and its operations are
-- real, computational code — not stubs. The five Tree obligations
-- (instantiated/extendable/valid/optimal/selfContained) plus genesisWinner
-- are POSTULATED rather than proved: they are open, unsolved problems even
-- upstream (ouroboros-praos-formal-spec's own Examples.Praos leaves the same
-- five as `{!!}` holes under `--allow-unsolved-metas`, and its extendTree
-- there looks like it actually violates `extendable` for blocks that fork
-- below the current chain tips). See the "Tree proof strategy" discussion —
-- postulating here unblocks wiring Leios.Base.Praos into the trace verifier
-- today; it's the same honesty tradeoff as this codebase's existing
-- `leadershipSchedule` postulate (LinearLeiosVerifier.agda).
--
-- NOT --safe (postulates below, and Leios.Base.Praos.Instance itself isn't).

open import Leios.Prelude hiding (_⊗_; prune; Hashable)
open import Leios.Abstract
open import Leios.VRF

open import Protocol.Prelude using (Default; def; _⊆ˢ_)
open import Protocol.BaseTypes using (Honesty; honest)

open import Data.Nat.Base using (NonZero; >-nonZero⁻¹; _<ᵇ_)
open import Data.Fin.Base using (fromℕ<)
open import Data.Bool.Base using (if_then_else_)
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_)
import Data.List.Relation.Unary.All as All'
import Data.List.Relation.Unary.AllPairs.Core as AllPairs'

module Leios.Base.Praos.Assumptions
  (a    : LeiosAbstract) (open LeiosAbstract a)
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  ⦃ DecEq-EBCert : DecEq EBCert ⦄
  (numParties : ℕ) ⦃ NonZero-numParties : NonZero numParties ⦄
  (winner : Fin numParties → ℕ → Type) ⦃ winner⁇² : winner ⁇² ⦄
  where

open import Leios.Base.Praos.Instance a vrf' numParties winner ⦃ winner⁇² = winner⁇² ⦄
open import Leios.Base.Praos a vrf' using (emptyRB)
open import Leios.Base a vrf' using (RankingBlock)

-- Party 0 always exists (numParties is NonZero); reused below for the
-- genesis block's producer and as the sole member of parties₀.
party₀ : Fin numParties
party₀ = fromℕ< (>-nonZero⁻¹ numParties)

open import Protocol.Block  ⦃ praosParams ⦄
open import Protocol.Crypto ⦃ praosParams ⦄ using (Hashable)

-- Ignores prev/slot/pid/announcedEB/ebCert, so distinct blocks with the same
-- RB payload collide — acceptable only because `valid`/`optimal` below are
-- postulated rather than proved from this definition.
instance
  praosHashableBlock : Hashable Block
  praosHashableBlock = record { hash = λ b → Hashable-Txs .hash (RankingBlock.txs (Block.txs b)) }

  praosDefaultBlock : Default Block
  praosDefaultBlock = record { def = mkBlock (Hashable-Txs .hash []) 0 emptyRB party₀ }

open import Protocol.Chain ⦃ praosParams ⦄
open import Protocol.Tree  ⦃ praosParams ⦄

TreeImpl : Type
TreeImpl = List Block

-- The longest chain reconstructable (via chainFromBlock) from any block in
-- the slot-bounded pool, ties broken arbitrarily. Protocol.Chain.prune is
-- Slot → Chain → Chain, but Chain = List Block = TreeImpl, so it applies.
candidateChains : ℕ → TreeImpl → List Chain
candidateChains sl t = L.map (λ b → chainFromBlock b pruned) pruned
  where pruned = prune sl t

longest : List Chain → Chain
longest = L.foldr (λ c best → if (length best <ᵇ length c) then c else best) []

praosBestChain : ℕ → TreeImpl → Chain
praosBestChain sl t = longest (candidateChains sl t)

praosAllBlocks : TreeImpl → List Block
praosAllBlocks = id

postulate
  -- Tree obligations (Protocol.Tree.Tree's five fields) — see header.
  praosInstantiated  : praosAllBlocks [ genesisBlock ] ≡ [ genesisBlock ]
  praosExtendable    : ∀ (t : TreeImpl) (b : Block) →
    praosAllBlocks (b ∷ t) ≡ˢ praosAllBlocks t ++ [ b ]
  praosValid         : ∀ (t : TreeImpl) (sl : ℕ) → praosBestChain sl t ✓
  praosOptimal       : ∀ (c : Chain) (t : TreeImpl) (sl : ℕ) →
      c ✓ → c ⊆ˢ L.filter ((_≤? sl) ∘ slot) (praosAllBlocks t)
    → ∣ c ∣ ≤ ∣ praosBestChain sl t ∣
  praosSelfContained : ∀ (t : TreeImpl) (sl : ℕ) →
    praosBestChain sl t ⊆ˢ L.filter ((_≤? sl) ∘ slot) (praosAllBlocks t)

instance
  praosTree : Tree TreeImpl
  praosTree = record
    { tree₀         = [ genesisBlock ]
    ; extendTree    = λ t b → b ∷ t
    ; allBlocks     = praosAllBlocks
    ; bestChain     = praosBestChain
    ; instantiated  = praosInstantiated
    ; extendable    = praosExtendable
    ; valid         = praosValid
    ; optimal       = praosOptimal
    ; selfContained = praosSelfContained
    }

open import Protocol.Assumptions ⦃ praosParams ⦄

postulate
  -- winner is an arbitrary caller-supplied predicate ("derived from the
  -- Leios VRF" per docs/praos-base-machine-sketch.md); nothing here can
  -- prove it holds for the genesis party/slot without a witness from the
  -- caller.
  praosGenesisWinner : winner (genesisBlock .pid) (genesisBlock .slot)

instance
  praosAssumptions : Assumptions
  praosAssumptions = record
    { TreeImpl          = TreeImpl
    ; AdversarialState  = ⊤
      -- All parties honest at this base layer: corruption is a
      -- Deployment-level concern (see the sketch doc's "Adversary &
      -- scheduling" note), out of scope for the honest-node wrapper.
    ; honestyOf         = λ _ → honest
      -- Unused: Deliver mints from the wrapper's own `pending` field, not
      -- from txSelection (see the sketch doc's "txSelection reconciliation"
      -- note).
    ; txSelection       = λ _ _ → emptyRB
    ; adversarialState₀ = tt
    ; parties₀          = [ party₀ ]
    ; processMsgsᶜ      = λ _ _ _ _ _ → [] , tt
    ; makeBlockᶜ        = λ _ _ _ _   → [] , tt
    ; Hashable-Block    = praosHashableBlock
    ; Default-Block     = praosDefaultBlock
    ; Tree-TreeImpl     = praosTree
    ; parties₀Uniqueness = AllPairs'._∷_ All'.[] AllPairs'.[]
    ; parties₀HasHonest  = here refl
    ; genesisBlockSlot   = refl
    ; genesisHonesty     = refl
    ; genesisWinner      = praosGenesisWinner
    }

-- Closes the gap docs/praos-base-machine-sketch.md flagged: with a concrete
-- Assumptions instance in hand, Leios.Base.Praos.Instance.WithAssumptions no
-- longer needs one as a bare module parameter.
open WithAssumptions ⦃ praosAssumptions ⦄ party₀ public using (praosNode)
