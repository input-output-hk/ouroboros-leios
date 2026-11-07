-- A concrete Assumptions instance for Leios.Base.Praos.Instance, closing the
-- module parameter that docs/praos-base-machine-sketch.md flagged as
-- missing: "no concrete Tree implementation with discharged laws exists
-- upstream, so it stays a parameter."
--
-- The block tree is Leios.Base.Praos.ChainSel: chain selection is
-- incremental, for chains of node-log size, and all five Protocol.Tree
-- obligations (instantiated/extendable/valid/optimal/selfContained) are
-- proved there; upstream leaves the same five as `{!!}` holes in its own
-- Examples.Praos.  Genesis is part of every tree's pool, so a valid best
-- chain always exists inside it.
--
-- genesisWinner is a module parameter (winner₀): the leader predicate is
-- caller-supplied, so only the caller can witness it at the genesis slot
-- (Defaults.agda makes slot 0 a universal winner — the machine never mints
-- at slot 0, since Deliver mints at `suc clock`).
--
-- NOT --safe: Leios.Base.Praos.Instance (Praos's chainFromBlock is
-- TERMINATING) — but this module contains no postulates.

open import Leios.Prelude hiding (_⊗_; prune; Hashable; hash)
open import Leios.Abstract
open import Leios.VRF

open import Protocol.Prelude using (Default; def; _⊆ˢ_)
open import Protocol.BaseTypes using (Honesty; honest)

open import Data.Nat.Base using (NonZero; >-nonZero⁻¹; z≤n)
open import Data.Fin.Base using (fromℕ<)
import Data.List.Relation.Unary.All as All'
import Data.List.Relation.Unary.AllPairs.Core as AllPairs'

import Leios.Base as LB

module Leios.Base.Praos.Assumptions
  (a    : LeiosAbstract) (open LeiosAbstract a)
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  ⦃ DecEq-EBCert : DecEq EBCert ⦄
  (numParties : ℕ) ⦃ NonZero-numParties : NonZero numParties ⦄
  (winner : Fin numParties → ℕ → Type) ⦃ winner⁇² : winner ⁇² ⦄
  (winner₀ : ∀ p → winner p 0)
  -- Content hash of a block (slot, producer, payload), used for prev-hash
  -- linkage. No Tree law depends on its injectivity, but callers should make
  -- it injective enough (e.g. include slot and producer) that reconstructed
  -- chains reflect real parenthood.
  (blockHash : ℕ → Fin numParties → LB.RankingBlock a vrf' → Hash)
  -- The party the node mints as.
  (self : Fin numParties)
  where

open import Leios.Base.Praos.Instance a vrf' numParties winner ⦃ winner⁇² = winner⁇² ⦄
open import Leios.Base.Praos a vrf' using (emptyRB)
open import Leios.Base a vrf' using (RankingBlock)

-- Party 0 always exists (numParties is NonZero); reused below for the
-- genesis block's producer and as the sole member of parties₀.
party₀ : Fin numParties
party₀ = fromℕ< (>-nonZero⁻¹ numParties)

open import Protocol.Block  ⦃ praosParams ⦄
open import Protocol.Crypto ⦃ praosParams ⦄ using (Hashable; hash)

instance
  praosHashableBlock : Hashable Block
  praosHashableBlock = record { hash = λ b → blockHash (b .slot) (b .pid) (b .txs) }

  praosDefaultBlock : Default Block
  praosDefaultBlock = record { def = mkBlock (Leios.Prelude.Hashable.hash Hashable-Txs []) 0 emptyRB party₀ }

open import Protocol.Chain ⦃ praosParams ⦄
open import Protocol.Tree  ⦃ praosParams ⦄

import Leios.Base.Praos.ChainSel ⦃ praosParams ⦄ as ChainSel

-- Genesis is a valid chain of slot 0.
TreeImpl : Type
TreeImpl = ChainSel.TreeImpl (winner₀ party₀) refl

instance
  praosTree : Tree TreeImpl
  praosTree = ChainSel.chainSelTree (winner₀ party₀) refl

open import Protocol.Assumptions ⦃ praosParams ⦄

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
    ; genesisWinner      = winner₀ party₀
    }

-- Closes the gap docs/praos-base-machine-sketch.md flagged: with a concrete
-- Assumptions instance in hand, Leios.Base.Praos.Instance.WithAssumptions no
-- longer needs one as a bare module parameter.
open WithAssumptions ⦃ praosAssumptions ⦄ self public using (praosNode)

-- Verifier-facing helpers for building tree blocks from trace data (the
-- PraosAbstract interface keeps Block abstract, so construction and hashing
-- need explicit exports).
mkPraosBlock : Hash → ℕ → RankingBlock → Fin numParties → Block
mkPraosBlock = mkBlock

praosBlockHash : Block → Hash
praosBlockHash = hash

genesisHash : Hash
genesisHash = hash genesisBlock

-- What a log records of a block the node mints, which leaves out the
-- payload: its parent and its slot.
praosHeader : Block → Hash × ℕ
praosHeader b = b .prev , b .slot
