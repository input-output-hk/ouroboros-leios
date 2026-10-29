-- Closes the remaining two gaps docs/praos-base-machine-sketch.md flagged
-- after Assumptions.agda: assembling Leios.Base.Praos.Node's `praosNode`
-- (from Assumptions.agda) all the way to a `BaseMachine`, and the
-- `producer`/`slotOf` wrinkle.
--
-- `Cert`/`VTy`/`initSlot`/`V-chkCerts`/`stake₀` are genuinely free choices —
-- the sketch doc already treats them as the caller's Cert-checking scheme
-- and stake distribution, unrelated to Praos itself ("Stake" / "Cert
-- checking" notes) — so they stay module parameters here, same as in
-- Leios.Base.Praos.Node itself, rather than something to "construct".
--
-- Neither `producer` nor `slotOf` can be recovered from a bare RankingBlock:
-- it carries no producer/pid and, since the pinned leios-spec dropped
-- RankingBlock.slot, no slot either (the Praos block around it has both, but
-- the payload projection loses them).  Both stay parameters, and both are
-- operationally inert for the trace verifier:
-- `Protocol.Semantics.processMsgsʰ` (absorbing delivered blocks) never
-- consults `winner`/producer identity, and `Blockchain.IsBlockchain`'s
-- `producer`/`slotOf` fields are only read by `Blockchain.Liveness.Transfer`
-- and `Network.Leios` (deployment-level theorem transport), modules
-- src/trace-parser.agda never imports.  Any placeholder is exercised by
-- nothing at runtime.
--
-- NOT --safe (Leios.Base.Praos.Instance/Assumptions aren't).

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.VRF

open import Data.Nat.Base using (NonZero)
import Leios.Base as LB

module Leios.Base.Praos.Machine
  (a    : LeiosAbstract) (open LeiosAbstract a)
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  ⦃ DecEq-EBCert : DecEq EBCert ⦄
  (numParties : ℕ) ⦃ NonZero-numParties : NonZero numParties ⦄
  (winner : Fin numParties → ℕ → Type) ⦃ winner⁇² : winner ⁇² ⦄
  -- Everyone wins the genesis slot; discharges the Assumptions record's
  -- genesisWinner. Harmless: the machine never mints at slot 0 (Deliver
  -- mints at `suc clock`).
  (winner₀ : ∀ p → winner p 0)
  -- Block-content hash for prev-linkage (see Assumptions.agda).
  (blockHash : ℕ → Fin numParties → LB.RankingBlock a vrf' → Hash)
  where

open import Leios.Base.Praos.Assumptions a vrf' numParties winner
  ⦃ winner⁇² = winner⁇² ⦄ winner₀ blockHash
  public using (praosNode; mkPraosBlock; praosBlockHash; genesisHash)
open import Leios.Base.Praos a vrf' using (module Node)
open import Leios.Base a vrf' using (RankingBlock; StakeDistr)
open import Leios.Blocks a using (EndorserBlock)

module Assembled
  (Cert VTy   : Type)
  (initSlot   : VTy → ℕ)
  (V-chkCerts : List PubKey → EndorserBlock × Cert → Bool)
  (stake₀     : StakeDistr)
  (producer   : RankingBlock → Fin numParties)
  (slotOf     : RankingBlock → ℕ)
  where

  private module PraosNode = Node praosNode Cert VTy initSlot V-chkCerts stake₀
  -- B' is what a SpecStructure consumer installs alongside praosBase.
  open PraosNode public using (B'; node)
  open PraosNode.Assemble numParties producer slotOf public
