-- A concrete Assumptions instance for Leios.Base.Praos.Instance, closing the
-- module parameter that docs/praos-base-machine-sketch.md flagged as
-- missing: "no concrete Tree implementation with discharged laws exists
-- upstream, so it stays a parameter."
--
-- All five Protocol.Tree obligations (instantiated/extendable/valid/optimal/
-- selfContained) are PROVED here — upstream leaves the same five as `{!!}`
-- holes in its own Examples.Praos. The design that makes them provable:
--
--   * allBlocks t = genesisBlock ∷ t — genesis is built into every tree, so
--     a valid best chain (which must end at genesis) always exists inside
--     the pool; with a bare pool, `valid` and `selfContained` conflict on
--     trees that lack genesis.
--   * bestChain enumerates every subsequence of the slot-descending sorting
--     of the (slot-pruned) pool, keeps those that pass a decidable validity
--     (_✓) and pool-membership check, and returns the longest, with
--     [ genesisBlock ] as base. `optimal` then holds because every valid
--     chain has strictly decreasing slots, hence IS a sublist of the sorted
--     pool (ListLemmas.decr-sub-sorted) and so is enumerated.
--
-- bestChain is exponential in the pool size: this is a REFERENCE
-- implementation for the spec-level machine (the verifier never executes it
-- — the SpecStructure's BM is only consumed by deployment-level theorem
-- transport). An efficient longest-valid-path implementation can replace it
-- later, with a proof relating the two.
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
open import Data.List.Relation.Binary.SetEquality using (_≡ˢ_; ⊆×⊇⇒≡ˢ)
import Data.List.Relation.Unary.All as All'
import Data.List.Relation.Unary.Any as Any'
import Data.List.Relation.Unary.AllPairs.Core as AllPairs'
import Data.List.Relation.Unary.Linked as Lkd
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties
  using (∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)

open import Leios.Base.Praos.ListLemmas

module Leios.Base.Praos.Assumptions
  (a    : LeiosAbstract) (open LeiosAbstract a)
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  ⦃ DecEq-EBCert : DecEq EBCert ⦄
  (numParties : ℕ) ⦃ NonZero-numParties : NonZero numParties ⦄
  (winner : Fin numParties → ℕ → Type) ⦃ winner⁇² : winner ⁇² ⦄
  (winner₀ : ∀ p → winner p 0)
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

-- Ignores prev/slot/pid/announcedEB/ebCert, so distinct blocks with the same
-- RB payload collide. That weakens which chains link up (hash collisions blur
-- parenthood) but no Tree law depends on hash injectivity: bestChain checks
-- validity of each candidate directly.
instance
  praosHashableBlock : Hashable Block
  praosHashableBlock = record { hash = λ b → Leios.Prelude.Hashable.hash Hashable-Txs (RankingBlock.txs (Block.txs b)) }

  praosDefaultBlock : Default Block
  praosDefaultBlock = record { def = mkBlock (Leios.Prelude.Hashable.hash Hashable-Txs []) 0 emptyRB party₀ }

open import Protocol.Chain ⦃ praosParams ⦄
open import Protocol.Tree  ⦃ praosParams ⦄

TreeImpl : Type
TreeImpl = List Block

-- Genesis is part of every tree's block set by construction.
praosAllBlocks : TreeImpl → List Block
praosAllBlocks t = genesisBlock ∷ t

-- ── Decision procedures for the candidate filter ────────────────────────

correctBlocks? : ∀ c → Dec (CorrectBlocks c)
correctBlocks? = All'.all? (λ b → ¿ CorrectBlock b ¿)

properlyLinked? : ∀ c → Dec (ProperlyLinked c)
properlyLinked? []            = no id
properlyLinked? (b ∷ [])      = b ≟ genesisBlock
properlyLinked? (b ∷ b′ ∷ bs) = (b .prev ≟ hash b′) ×-dec properlyLinked? (b′ ∷ bs)

decreasingSlots? : ∀ c → Dec (DecreasingSlots c)
decreasingSlots? []            = yes Lkd.[]
decreasingSlots? (b ∷ [])      = yes Lkd.[-]
decreasingSlots? (b ∷ b′ ∷ bs) with b′ .slot <? b .slot | decreasingSlots? (b′ ∷ bs)
... | yes p | yes q = yes (p Lkd.∷ q)
... | no ¬p | _     = no λ where (r Lkd.∷ _) → ¬p r
... | yes _ | no ¬q = no λ where (_ Lkd.∷ s) → ¬q s

opaque
  unfolding _✓

  ✓? : ∀ c → Dec (c ✓)
  ✓? c = correctBlocks? c ×-dec (properlyLinked? c ×-dec decreasingSlots? c)

  gb✓ : [ genesisBlock ] ✓
  gb✓ = All'._∷_ (winner₀ party₀) All'.[] , refl , Lkd.[-]

  ✓⇒decr : ∀ {c} → c ✓ → DecreasingSlots c
  ✓⇒decr (_ , _ , ds) = ds

sub? : ∀ (c ys : List Block) → Dec (All'.All (_∈ˡ ys) c)
sub? c ys = All'.all? (λ x → Any'.any? (x ≟_) ys) c

-- ── bestChain: longest checked candidate ────────────────────────────────

open MaxBy {B = Chain} length
open SortDesc _≟_ slot

pruned : ℕ → TreeImpl → List Block
pruned sl t = L.filter ((_≤? sl) ∘ slot) (praosAllBlocks t)

Candidate : ℕ → TreeImpl → Chain → Type
Candidate sl t c = (c ✓) × All'.All (_∈ˡ pruned sl t) c

candidate? : ∀ sl t c → Dec (Candidate sl t c)
candidate? sl t c = ✓? c ×-dec sub? c (pruned sl t)

candidates : ℕ → TreeImpl → List Chain
candidates sl t = L.filter (candidate? sl t) (subseqs (sortDesc (pruned sl t)))

praosBestChain : ℕ → TreeImpl → Chain
praosBestChain sl t = maxBy [ genesisBlock ] (candidates sl t)

-- ── The Tree laws ────────────────────────────────────────────────────────

praosExtendable : ∀ (t : TreeImpl) (b : Block) →
  praosAllBlocks (b ∷ t) ≡ˢ praosAllBlocks t ++ [ b ]
praosExtendable t b = ⊆×⊇⇒≡ˢ to′ from′
  where
    -- praosAllBlocks t ++ [ b ] reduces to gb ∷ (t ++ [ b ])
    to′ : praosAllBlocks (b ∷ t) ⊆ˢ praosAllBlocks t ++ [ b ]
    to′ (here refl)         = here refl
    to′ (there (here refl)) = there (∈-++⁺ʳ t (here refl))
    to′ (there (there p))   = there (∈-++⁺ˡ p)

    from′ : praosAllBlocks t ++ [ b ] ⊆ˢ praosAllBlocks (b ∷ t)
    from′ (here refl) = here refl
    from′ (there q) with ∈-++⁻ t q
    ... | inj₁ p           = there (there p)
    ... | inj₂ (here refl) = there (here refl)

praosValid : ∀ (t : TreeImpl) (sl : ℕ) → praosBestChain sl t ✓
praosValid t sl with maxBy-mem [ genesisBlock ] (candidates sl t)
... | inj₁ eq  = subst _✓ (sym eq) gb✓
... | inj₂ mem =
  ∈-filter⁻ (candidate? sl t) {xs = subseqs (sortDesc (pruned sl t))} mem .proj₂ .proj₁

praosSelfContained : ∀ (t : TreeImpl) (sl : ℕ) →
  praosBestChain sl t ⊆ˢ L.filter ((_≤? sl) ∘ slot) (praosAllBlocks t)
praosSelfContained t sl with maxBy-mem [ genesisBlock ] (candidates sl t)
... | inj₁ eq  = subst (_⊆ˢ pruned sl t) (sym eq) gb⊆
  where
    -- pruned sl t head-reduces to gb ∷ … since slot gb = 0 ≤ sl definitionally
    gb⊆ : [ genesisBlock ] ⊆ˢ pruned sl t
    gb⊆ (here refl) = here refl
... | inj₂ mem = λ p∈ →
  All'.lookup
    (∈-filter⁻ (candidate? sl t) {xs = subseqs (sortDesc (pruned sl t))} mem .proj₂ .proj₂)
    p∈

praosOptimal : ∀ (c : Chain) (t : TreeImpl) (sl : ℕ) →
    c ✓ → c ⊆ˢ L.filter ((_≤? sl) ∘ slot) (praosAllBlocks t)
  → ∣ c ∣ ≤ ∣ praosBestChain sl t ∣
praosOptimal c t sl c✓ c⊆ = maxBy-≥ [ genesisBlock ] (candidates sl t) c∈cands
  where
    prn = pruned sl t

    c∈prn : All'.All (_∈ˡ prn) c
    c∈prn = All'.tabulate c⊆

    c∈srt : All'.All (_∈ˡ sortDesc prn) c
    c∈srt = All'.map (sortDesc-∈ prn) c∈prn

    c∈cands : c ∈ˡ candidates sl t
    c∈cands =
      ∈-filter⁺ (candidate? sl t)
        (subseqs-complete
          (decr-sub-sorted (✓⇒decr c✓) c∈srt (sortDesc-sorted prn)))
        (c✓ , c∈prn)

instance
  praosTree : Tree TreeImpl
  praosTree = record
    { tree₀         = []
    ; extendTree    = λ t b → b ∷ t
    ; allBlocks     = praosAllBlocks
    ; bestChain     = praosBestChain
    ; instantiated  = refl
    ; extendable    = praosExtendable
    ; valid         = praosValid
    ; optimal       = praosOptimal
    ; selfContained = praosSelfContained
    }

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
open WithAssumptions ⦃ praosAssumptions ⦄ party₀ public using (praosNode)
