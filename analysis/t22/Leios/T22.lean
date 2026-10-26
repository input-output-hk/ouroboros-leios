import Leios.Model
import Mathlib.Tactic.Linarith

/-!
# Threat T22: selective data withholding

The threat model lists T22 as "selectively withhold data from most honest nodes", with effect
"allow certification, delay block propagation" and mitigation "`L_diff` parameter sizing". The
adversary releases the EB closure just in time to just enough honest committee members for a
certificate to form, and to nobody else. The certificate then lands in an RB that most honest
nodes cannot select, because they lack the EB.

This file makes the mitigation precise in both directions.

* `t22_cannot_happen`: if `voteRecvOffset + D ≤ certGap + Δ`, then in every world with a
  certificate and with the network axiom `HonestDiffuse`, no certificate RB is late at any
  honest node. Under the prototype's voting rule the condition is `D ≤ Ldiff + Δ`.
* `t22_can_happen`: if that inequality fails, the attack goes through. We build the world the
  threat model describes and check that it satisfies the network axiom, has a certificate,
  and is late at an honest node.

The argument for the first is three lines. A certificate needs stake `τ ≥ 1/2` and the
adversary has less than `1/2`, so some voter is honest. An honest voter holds the EB by the
vote deadline. By `HonestDiffuse`, every honest node holds it `D` slots later, which is before
`c + Δ` for every admissible certificate slot `c`.
-/

namespace Leios

namespace World

open Finset

variable {n : ℕ} (w : World n) (p : Params)

/-! ## T22 cannot happen when `L_diff` is large enough -/

/-- The adversary's votes are worth at most its stake: `advVotes ⊆ corrupt`. -/
lemma stakeOf_advVotes_le : w.stakeOf w.advVotes ≤ w.advStake :=
  -- `advVotes ⊆ corrupt ∩ committee ⊆ corrupt`, then monotonicity of `stakeOf`
  w.stakeOf_mono (w.advVotes_sub.trans inter_subset_left)

/-- A certificate contains an honest vote.

If no honest party voted, the voters are exactly the adversary's, whose stake is below `τ` by
`advStake_lt_τ`, contradicting the quorum. -/
theorem cert_has_honest_voter (hcert : w.Certified p) : ∃ i, i ∈ w.honestVoters p := by
  -- suppose no honest voter exists; then the set of honest voters is empty
  by_contra h
  have hempty : w.honestVoters p = ∅ := eq_empty_of_forall_notMem fun i hi => h ⟨i, hi⟩
  -- chain: the quorum is met by the voters, who are then just the adversary's, whose stake is
  -- below the quorum; so `τ < τ`
  have : p.τ < p.τ :=
    calc p.τ ≤ w.stakeOf (w.voters p) := hcert
      _ = w.stakeOf w.advVotes := by simp [voters, hempty]
      _ ≤ w.advStake := w.stakeOf_advVotes_le
      _ < p.τ := w.advStake_lt_τ p
  exact lt_irrefl _ this

/-- With a certificate, every honest node holds the EB by `D` slots after the vote deadline.

The honest voter of `cert_has_honest_voter` held the EB by the deadline; `HonestDiffuse` carries
it from that one node to every honest node within `D`. -/
theorem recv_le_of_certified (hcert : w.Certified p) (hdiff : w.HonestDiffuse p) {j : Fin n}
    (hj : w.honest j) : w.recv j ≤ ((w.voteRecvDeadline p + p.D : ℕ) : ℕ∞) := by
  -- pick an honest voter `i`
  obtain ⟨i, hi⟩ := w.cert_has_honest_voter p hcert
  -- the network axiom with `t := voteRecvDeadline`: `i` holds the EB by `t`, so `j` holds it
  -- by `t + D`
  exact hdiff i j (w.honest_of_mem_honestVoters p hi) hj _ (w.recv_le_of_mem_honestVoters p hi)

/-- **T22 cannot happen.** If the EB diffusion time fits into the diffusion period plus the
Praos bound, `voteRecvOffset + D ≤ certGap + Δ`, then no certificate RB is late at any honest
node, in every world with a certificate and the network axiom.

The certificate slot `c` is any slot at or after `minCertSlot`; a later `c` only gives the EB
more time. -/
theorem t22_cannot_happen (hcert : w.Certified p) (hdiff : w.HonestDiffuse p)
    (hD : p.voteRecvOffset + p.D ≤ p.certGap + p.Δ) {c : ℕ} (hc : w.minCertSlot p ≤ c) :
    ¬ w.Harm p c := by
  -- assume harm: an honest `j` with `c + Δ < recv j`
  rintro ⟨j, hj, hlate⟩
  -- `deadline + D ≤ c + Δ` is the parameter condition `hD` shifted by `s`, since
  -- `deadline = s + voteRecvOffset` and `s + certGap = minCertSlot ≤ c`
  have hle : w.voteRecvDeadline p + p.D ≤ c + p.Δ := by
    unfold voteRecvDeadline minCertSlot at *
    omega
  -- chain: `c + Δ < recv j ≤ deadline + D ≤ c + Δ`, so `c + Δ < c + Δ`
  have : ((c + p.Δ : ℕ) : ℕ∞) < ((c + p.Δ : ℕ) : ℕ∞) :=
    calc ((c + p.Δ : ℕ) : ℕ∞) < w.recv j := hlate
      _ ≤ ((w.voteRecvDeadline p + p.D : ℕ) : ℕ∞) := w.recv_le_of_certified p hcert hdiff hj
      _ ≤ ((c + p.Δ : ℕ) : ℕ∞) := by exact_mod_cast hle
  exact lt_irrefl _ this

/-- `t22_cannot_happen` under the prototype's voting rule, `voteRecvOffset = voteDeadlineOffset`
(`hproto`, which `Params.prototype` satisfies by definition). The condition then reads
`D ≤ Ldiff + Δ`: the EB must reach everyone within the diffusion period plus the Praos bound. -/
theorem t22_cannot_happen_prototype (hproto : p.voteRecvOffset = p.voteDeadlineOffset)
    (hcert : w.Certified p) (hdiff : w.HonestDiffuse p) (hD : p.D ≤ p.Ldiff + p.Δ)
    {c : ℕ} (hc : w.minCertSlot p ≤ c) : ¬ w.Harm p c :=
  -- the general theorem; with `voteRecvOffset = 3 Lhdr + Lvote` and
  -- `certGap = 3 Lhdr + Lvote + Ldiff`, its condition is `hD` plus `3 Lhdr + Lvote` on both sides
  w.t22_cannot_happen p hcert hdiff
    (by unfold Params.voteDeadlineOffset Params.certGap at *; omega) hc

-- `Params.prototype` satisfies `hproto` by definition.
example (Lhdr Lvote Ldiff : ℕ) (τ : ℚ) (hτ : 1 / 2 ≤ τ) (Δ D : ℕ) :
    (Params.prototype Lhdr Lvote Ldiff τ hτ Δ D).voteRecvOffset =
      (Params.prototype Lhdr Lvote Ldiff τ hτ Δ D).voteDeadlineOffset := rfl

/-! ## T22 can happen when `L_diff` is too small

The world the threat model describes. Starting from any pipeline `w`, the adversary releases the
EB to a chosen set `V` of honest committee members exactly at the last slot at which they still
vote, and to everyone else `D` slots later, the latest the network axiom allows. It adds the
votes of every corrupt committee member. -/

/-- Corrupt committee members: the votes the adversary can cast itself. -/
def advCommittee : Finset (Fin n) := w.corrupt ∩ w.committee

/-- The T22 execution built on top of `w`: only `recv` and `advVotes` change. -/
def t22World (V : Finset (Fin n)) : World n :=
  { w with
    recv := fun i =>
      if i ∈ V then ((w.s + p.voteRecvOffset : ℕ) : ℕ∞)
      else ((w.s + p.voteRecvOffset + p.D : ℕ) : ℕ∞)
    advVotes := w.advCommittee
    advVotes_sub := subset_rfl }

/-- The T22 execution keeps the stake of `w`, so the stake of any set is unchanged. -/
lemma t22World_stakeOf (V S : Finset (Fin n)) : (w.t22World p V).stakeOf S = w.stakeOf S := rfl

/-- The T22 execution respects the network axiom: every arrival lies in a window of length `D`. -/
lemma t22World_honestDiffuse (V : Finset (Fin n)) : (w.t22World p V).HonestDiffuse p := by
  -- unfold the axiom: given `i`, `j`, a slot `t` with `recv i ≤ t`, show `recv j ≤ t + D`
  intro i j _ _ t ht
  -- replace `recv` by its definition in the witness world (an `if i ∈ V then … else …`)
  dsimp only [t22World] at ht ⊢
  -- case on whether `i ∈ V` and whether `j ∈ V`; in each case drop the casts and finish by
  -- linear arithmetic, since both arrival times lie in `[s + offset, s + offset + D]`
  split_ifs at ht ⊢ <;> norm_cast at ht ⊢ <;> omega

/-- The T22 execution has a certificate, provided the adversary chose `V` well:

* `hV`: `V` consists of honest committee members, and
* `hτ`: the stake of `V` plus the adversary's own committee stake reaches the quorum.

Proof sketch. Every member of `V` votes, since it holds the EB exactly at the deadline. Every
corrupt committee member votes, by construction of `t22World`. The two groups are disjoint,
so the voters' stake is at least `stakeOf V + stakeOf advCommittee`, which is at least `τ`. -/
lemma t22World_certified (V : Finset (Fin n))
    (hV : V ⊆ w.committee \ w.corrupt)
    (hτ : p.τ ≤ w.stakeOf V + w.stakeOf w.advCommittee) :
    (w.t22World p V).Certified p := by
  -- Step 1: every member of `V` is an honest voter: in the committee and honest (from `hV`),
  -- and holding the EB by the deadline (its arrival time is exactly the deadline).
  have hV_votes : V ⊆ (w.t22World p V).honestVoters p := by
    intro i hi
    obtain ⟨hcom, hhon⟩ := mem_sdiff.1 (hV hi)
    rw [mem_honestVoters]
    exact ⟨hcom, hhon, by simp [t22World, voteRecvDeadline, hi]⟩
  -- Step 2: so `V ∪ advCommittee ⊆ voters`, the adversary's votes being `advCommittee`.
  have hsub : V ∪ w.advCommittee ⊆ (w.t22World p V).voters p :=
    union_subset_union hV_votes subset_rfl
  -- Step 3: `V` (honest) and `advCommittee` (corrupt) are disjoint.
  have hdisj : Disjoint V w.advCommittee :=
    disjoint_left.2 fun i hi hi' => (mem_sdiff.1 (hV hi)).2 (mem_inter.1 hi').1
  -- Step 4: chain the inequalities. `Certified` unfolds to `τ ≤ stakeOf voters`, and the
  -- witness world's `stakeOf` is `w.stakeOf` (`t22World_stakeOf`).
  show p.τ ≤ (w.t22World p V).stakeOf _
  rw [t22World_stakeOf]
  calc p.τ ≤ w.stakeOf V + w.stakeOf w.advCommittee := hτ
    _ = w.stakeOf (V ∪ w.advCommittee) := (w.stakeOf_union_of_disjoint hdisj).symm
    _ ≤ w.stakeOf ((w.t22World p V).voters p) := w.stakeOf_mono hsub

/-- The T22 execution is late at every honest node outside `V`, at the earliest certificate
slot, as soon as `certGap + Δ < voteRecvOffset + D`. -/
lemma t22World_harm (V : Finset (Fin n)) (hD : p.certGap + p.Δ < p.voteRecvOffset + p.D)
    {j : Fin n} (hj : w.honest j) (hjV : j ∉ V) :
    (w.t22World p V).Harm p ((w.t22World p V).minCertSlot p) := by
  -- the late node is `j`; it remains to show `minCertSlot + Δ < recv j`
  refine ⟨j, hj, ?_⟩
  -- unfold the witness world and `minCertSlot`; since `j ∉ V` the `if` picks the late arrival
  simp only [t22World, minCertSlot, hjV, ↓reduceIte]
  -- drop the casts to `ℕ∞`
  norm_cast
  -- `s + certGap + Δ < s + voteRecvOffset + D` is `hD` plus `s`
  omega

/-- **T22 can happen.** If `certGap + Δ < voteRecvOffset + D`, the attack goes through: starting
from any pipeline `w`, the adversary picks honest committee members `V` whose stake together
with its own committee stake reaches the quorum (`hV`, `hτ`), releases the EB to them at the
vote deadline and to everyone else `D` slots later (`t22World`), and the result is an execution
that

* respects the network axiom `HonestDiffuse`,
* has a certificate, and
* is late at every honest node outside `V` (here witnessed by `j`), already at the earliest
  certificate slot.

`t22World` keeps the stake, corrupt set, committee and announcing slot of `w`; only the EB
arrival times and the adversary's votes are chosen by the attack. -/
theorem t22_can_happen (hD : p.certGap + p.Δ < p.voteRecvOffset + p.D)
    (V : Finset (Fin n)) (hV : V ⊆ w.committee \ w.corrupt)
    (hτ : p.τ ≤ w.stakeOf V + w.stakeOf w.advCommittee)
    {j : Fin n} (hj : w.honest j) (hjV : j ∉ V) :
    (w.t22World p V).HonestDiffuse p ∧
    (w.t22World p V).Certified p ∧
    (w.t22World p V).Harm p ((w.t22World p V).minCertSlot p) :=
  -- the three lemmas above, one per conjunct
  ⟨w.t22World_honestDiffuse p V, w.t22World_certified p V hV hτ, w.t22World_harm p V hD hj hjV⟩

end World

end Leios
