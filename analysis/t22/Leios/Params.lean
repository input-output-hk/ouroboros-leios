import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Protocol parameters of Linear Leios

Times are measured in slots (`ℕ`). With `s` the slot of the ranking block (RB) announcing an
endorser block (EB), one pipeline is:

* `[s, s + 3·Lhdr]`: equivocation detection, the announcing header travels the network;
* `[s + 3·Lhdr, s + 3·Lhdr + Lvote]`: voting window for committee members holding the EB;
* `Ldiff` further slots of diffusion;
* from `s + 3·Lhdr + Lvote + Ldiff` on, an RB directly extending the announcing RB may carry a
  certificate (votes worth at least a fraction `τ` of the stake) instead of transactions.

`Δ` and `D` describe the environment: the Praos delivery bound for RBs, and the worst-case
time for an EB to reach every honest node. See the README for the modelling assumptions.
-/

namespace Leios

structure Params where
  /-- Announcement period: time for an RB header to reach the network. -/
  Lhdr : ℕ
  /-- Vote period: length of the voting window. -/
  Lvote : ℕ
  /-- Diffusion period: slots reserved after voting for the EB to reach everyone. -/
  Ldiff : ℕ
  /-- Quorum: a certificate needs votes worth at least this fraction of the stake. -/
  τ : ℚ
  /-- Assumption: the quorum is at least one half (three quarters in the CIP). With an honest
  majority this makes a certificate evidence of an honest vote. -/
  τ_ge_half : 1 / 2 ≤ τ
  /-- Praos delivery bound: every honest node can select an RB within `Δ` slots of its slot,
  provided it holds whatever else that RB needs. -/
  Δ : ℕ
  /-- Worst-case time for an EB held by one honest node to be held, with its closure validated,
  by every honest node. Kept separate from `Δ` because EBs are much larger than RBs; the
  theorems bound by how much `D` may exceed `Δ`. -/
  D : ℕ
  /-- An honest committee member votes only if it held the EB by slot `s + voteRecvOffset`.
  See `Params.prototype` and `Params.spec` for the two rules in circulation. -/
  voteRecvOffset : ℕ

namespace Params

variable (p : Params)

/-- Offset of the last voting slot from the announcing slot. -/
def voteDeadlineOffset : ℕ := 3 * p.Lhdr + p.Lvote

/-- Minimal distance between the announcing RB and an RB carrying its certificate: an RB in
slot `c` may carry the certificate for the EB announced in slot `s` only if `s + certGap ≤ c`. -/
def certGap : ℕ := 3 * p.Lhdr + p.Lvote + p.Ldiff

/-- Prototype voting rule: vote as long as the EB is held by the vote deadline. This is the
lenient rule and hence the worst case for the attack. -/
def prototype (Lhdr Lvote Ldiff : ℕ) (τ : ℚ) (τ_ge_half : 1 / 2 ≤ τ) (Δ D : ℕ) : Params :=
  { Lhdr, Lvote, Ldiff, τ, τ_ge_half, Δ, D, voteRecvOffset := 3 * Lhdr + Lvote }

/-- Agda/CIP voting rule: vote only if the EB arrived within `Lhdr` of the announcing slot. -/
def spec (Lhdr Lvote Ldiff : ℕ) (τ : ℚ) (τ_ge_half : 1 / 2 ≤ τ) (Δ D : ℕ) : Params :=
  { Lhdr, Lvote, Ldiff, τ, τ_ge_half, Δ, D, voteRecvOffset := Lhdr }

end Params

/-! Sanity checks with the CIP glossary values (`L_hdr = 1`, `L_vote = 4`, `L_diff = 7`,
`τ = 3/4`, `Δ = 5`, `D = 12`); they guard the definitions above against typos. -/

example : (Params.prototype 1 4 7 (3 / 4) (by norm_num) 5 12).certGap = 14 := by decide
example : (Params.spec 1 4 7 (3 / 4) (by norm_num) 5 12).certGap = 14 := by decide
example : (Params.prototype 1 4 7 (3 / 4) (by norm_num) 5 12).voteRecvOffset = 7 := by decide
example : (Params.spec 1 4 7 (3 / 4) (by norm_num) 5 12).voteRecvOffset = 1 := by decide

end Leios
