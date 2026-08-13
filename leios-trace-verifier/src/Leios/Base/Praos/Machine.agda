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
-- `slotOf` turns out NOT to need the doc's Option 1/2 redesign: the pinned
-- leios-spec here still has RankingBlock.slot (the newer, `main`-branch
-- shape the doc was written against dropped it), so `slotOf := RankingBlock.slot`
-- is immediate.
--
-- `producer` genuinely can't be recovered from a bare RankingBlock (no
-- producer/pid field survives payload projection), so it stays a parameter
-- too — but it's operationally inert for the trace verifier either way:
-- `Protocol.Semantics.processMsgsʰ` (absorbing delivered blocks) never
-- consults `winner`/producer identity, and `Blockchain.IsBlockchain`'s
-- `producer`/`slotOf` fields are only read by `Blockchain.Liveness.Transfer`
-- and `Network.Leios` (deployment-level theorem transport) — modules
-- src/trace-parser.agda never imports. Any placeholder (e.g. the existing
-- stub's `λ _ → Fin.zero`) is exercised by nothing at runtime.
--
-- NOT --safe (Leios.Base.Praos.Instance/Assumptions aren't).

open import Leios.Prelude hiding (_⊗_)
open import Leios.Abstract
open import Leios.VRF

open import Data.Nat.Base using (NonZero)

module Leios.Base.Praos.Machine
  (a    : LeiosAbstract) (open LeiosAbstract a)
  (vrf' : LeiosVRF a   ) (open LeiosVRF vrf'  )
  ⦃ DecEq-EBCert : DecEq EBCert ⦄
  (numParties : ℕ) ⦃ NonZero-numParties : NonZero numParties ⦄
  (winner : Fin numParties → ℕ → Type) ⦃ winner⁇² : winner ⁇² ⦄
  where

open import Leios.Base.Praos.Assumptions a vrf' numParties winner
  ⦃ winner⁇² = winner⁇² ⦄
  using (praosNode)
open import Leios.Base.Praos a vrf' using (module Node)
open import Leios.Base a vrf' using (RankingBlock; StakeDistr)
open import Leios.Blocks a using (EndorserBlock)

module Assembled
  (Cert VTy   : Type)
  (initSlot   : VTy → ℕ)
  (V-chkCerts : List PubKey → EndorserBlock × Cert → Bool)
  (stake₀     : StakeDistr)
  (producer   : RankingBlock → Fin numParties)
  where

  private module PraosNode = Node praosNode Cert VTy initSlot V-chkCerts stake₀
  -- B' is what a SpecStructure consumer installs alongside praosBase.
  open PraosNode public using (B'; node)
  open PraosNode.Assemble numParties producer RankingBlock.slot public
