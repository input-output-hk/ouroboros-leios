import Leios.T22
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum

/-!
# How unlikely is T22

`t22_can_happen` shows that when `D` exceeds `Ldiff + Δ` the attack is possible. This file asks
how likely it is to succeed, and answers with a bound that depends on nothing but the leader
lottery of Praos.

**Conclusion.** If `Ldiff` is set too small by `k` slots, that is `D = Ldiff + Δ + k`, then the
attack can only do damage if the Praos lottery elects a leader in `k` specific slots, which
happens with probability at most `1 − (1 − f)^k`, however the adversary schedules the EB. On
mainnet `f = 1/20`, so one slot short costs at most about five percent, two slots about ten,
and the bound goes to zero as `k` does, recovering `t22_cannot_happen`. The bound is on how
often the timing lines up, not on what the attack costs once it does.

The two steps below are joined in prose, not in one Lean statement: joining them formally
would need the leader lottery to be part of `World`, which this model does not have.

**Step 1, deterministic.** Even when the network is slow, a harmful certificate RB cannot sit
just anywhere. It must be at or after `minCertSlot`, and `recv_le_of_certified` says every
honest node holds the EB by `s + voteRecvOffset + D`; so the harm needs a certificate RB at a
slot `c` with `c + Δ < s + voteRecvOffset + D`. That leaves the window

    harmWindow = [ s + certGap , s + voteRecvOffset + D − Δ )

of `(voteRecvOffset + D) − (certGap + Δ)` slots, which is `D − (Ldiff + Δ)` under the
prototype's rule. Call `Ldiff + Δ` the budget: the slots the protocol grants the EB to travel
from the last honest voter to everyone. The window is the overshoot of `D` over the budget.
With the glossary values the budget is `7 + 5 = 12`; if `D = 14`, the EB may arrive two slots
late and only a certificate RB in slot `s + 14` or `s + 15` is harmful, since from `s + 16` on
the EB has caught up. A two-slot overshoot leaves a two-slot window.

**Step 2, probabilistic.** A certificate RB can only be produced in a slot that has a leader.
In Praos each slot has a leader independently with probability `f` (the active slot
coefficient, `1/20` on mainnet). The probability that at least one of `k` given slots has a
leader is `1 − (1 − f)^k`. We prove this in a small finite model: an outcome is a function
`Fin k → Bool` saying which slots have a leader, with the product weight.

**Together.** Any event that implies "some slot of the window has a leader" has probability
at most `1 − (1 − f)^k`. The event "the attack produces a late certificate RB" is such an
event, by step 1. With `f = 1/20` and a two-slot overshoot the bound is `39/400`, under ten
percent. This is the sense in which T22 is unlikely when `Ldiff` is slightly too small, and it
degrades gracefully: each extra slot of overshoot costs a factor `1 − f`.

Two remarks on what the bound covers. The lottery counts every leader, honest or adversarial;
an adversarial leader in the window is the attacker's best case, and the bound includes it.
The bound is per pipeline and does not assume the lottery is hidden from the adversary: in
Praos a party can evaluate its own VRF ahead of time, so an adversary may launch the attack
only in pipelines where it already knows it has a leader in the window. The bound then says
how often such pipelines occur, not that a launched attack fails with that probability.
-/

namespace Leios

namespace World

open Finset

variable {n : ℕ} (w : World n) (p : Params)

/-! ## Step 1: a harmful certificate RB sits in a short window -/

/-- With a certificate and the network axiom, harm at slot `c` forces `c + Δ` below the slot by
which every honest node holds the EB. -/
theorem harm_slot_lt (hcert : w.Certified p) (hdiff : w.HonestDiffuse p) {c : ℕ}
    (hharm : w.Harm p c) : c + p.Δ < w.s + p.voteRecvOffset + p.D := by
  -- the late honest node `j`, with `c + Δ < recv j`
  obtain ⟨j, hj, hlate⟩ := hharm
  -- `recv j ≤ voteRecvDeadline + D` since there is a certificate
  have hrecv := w.recv_le_of_certified p hcert hdiff hj
  -- chain the two: `c + Δ < voteRecvDeadline + D`, still in `ℕ∞`
  have := lt_of_lt_of_le hlate hrecv
  -- expose `s + voteRecvOffset`
  unfold voteRecvDeadline at this
  -- drop the casts: a strict inequality between casts of naturals is one between the naturals
  exact_mod_cast this

/-- The slots at which a certificate RB can be harmful. -/
def harmWindow : Finset ℕ := Finset.Ico (w.minCertSlot p) (w.s + p.voteRecvOffset + p.D - p.Δ)

/-- A harmful certificate RB sits in the harm window. -/
theorem mem_harmWindow_of_harm (hcert : w.Certified p) (hdiff : w.HonestDiffuse p) {c : ℕ}
    (hc : w.minCertSlot p ≤ c) (hharm : w.Harm p c) : c ∈ w.harmWindow p := by
  -- the upper bound on `c` from the previous theorem
  have := w.harm_slot_lt p hcert hdiff hharm
  -- membership in `Ico a b` is `a ≤ c ∧ c < b`
  rw [harmWindow, mem_Ico]
  -- lower bound is `hc`, upper bound is `this` after moving `Δ` across (truncated subtraction)
  omega

/-- The harm window has `(voteRecvOffset + D) − (certGap + Δ)` slots: the overshoot of the EB
diffusion time over its budget. Under the prototype's rule this is `D − (Ldiff + Δ)`. -/
theorem card_harmWindow :
    (w.harmWindow p).card = p.voteRecvOffset + p.D - (p.certGap + p.Δ) := by
  -- `#(Ico a b) = b − a`, then expose `minCertSlot = s + certGap`
  rw [harmWindow, Nat.card_Ico, minCertSlot]
  -- `(s + off + D − Δ) − (s + certGap) = off + D − (certGap + Δ)`, with truncation on both sides
  omega

end World

/-! ## Step 2: the leader lottery over a window of `k` slots -/

namespace Lottery

open Finset

variable {k : ℕ} (f : ℚ)

/-- Weight of an outcome: each slot with a leader contributes `f`, each without `1 − f`. -/
def wt (x : Fin k → Bool) : ℚ := ∏ j, if x j then f else 1 - f

/-- Probability of an event: the total weight of its outcomes. -/
noncomputable def prob (E : Set (Fin k → Bool)) : ℚ := ∑ x, E.indicator (wt f) x

/-- The event that some slot of the window has a leader. -/
def someLeader : Set (Fin k → Bool) := {x | ∃ j, x j = true}

/-- The event that no slot of the window has a leader: the single outcome `fun _ => false`. -/
def noLeader : Set (Fin k → Bool) := {x | ∀ j, x j = false}

/-- Weights are non-negative when `0 ≤ f ≤ 1`. -/
lemma wt_nonneg (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (x : Fin k → Bool) : 0 ≤ wt f x :=
  -- a product of non-negative factors; each factor is `f` or `1 − f`, both non-negative
  prod_nonneg fun j _ => by split_ifs <;> linarith

/-- The weights sum to one: expanding the product over slots gives `(f + (1 − f))^k`. -/
lemma sum_wt : ∑ x : Fin k → Bool, wt f x = 1 := by
  -- Mathlib: `(∑ b, g b)^k` is the sum over all `k`-tuples of the product of `g`;
  -- here `∑ b, g b = f + (1 − f)`
  have h := Finset.sum_pow' (univ : Finset Bool) (fun b => if b then f else 1 - f) k
  -- the tuples range over `piFinset (fun _ => univ)`, which is all of `Fin k → Bool`
  rw [Fintype.piFinset_univ] at h
  -- our weight is exactly that product
  unfold wt
  -- `simp` evaluates `(f + (1 − f))^k = 1^k = 1` on the left of `h`; the rest matches
  simpa using h.symm

/-- The outcome without any leader has weight `(1 − f)^k`. -/
lemma prob_noLeader : prob f (noLeader (k := k)) = (1 - f) ^ k := by
  -- the probability is a sum of indicators over all outcomes
  unfold prob
  -- only the all-`false` outcome contributes: `sum_eq_single` reduces the sum to that term,
  -- leaving two side goals (other terms vanish; the chosen term is in the index set)
  rw [sum_eq_single (fun _ => false)]
  -- the term itself: the all-`false` outcome is in `noLeader` and its weight is `(1 − f)^k`
  · simp [noLeader, wt]
  -- any other outcome `x` is not in `noLeader`, so its indicator is `0`
  · intro x _ hx
    apply Set.indicator_of_notMem
    -- if `x` were in `noLeader`, every coordinate would be `false`, so `x` would be the
    -- all-`false` function, contradicting `hx`
    intro h
    exact hx (funext h)
  -- the all-`false` outcome is in `univ`
  · simp

/-- The probability that some slot has a leader is `1 − (1 − f)^k`. -/
lemma prob_someLeader : prob f (someLeader (k := k)) = 1 - (1 - f) ^ k := by
  -- `someLeader` is the complement of `noLeader`: "some coordinate is true" is "not all false"
  have hcompl : someLeader (k := k) = (noLeader (k := k))ᶜ := by
    ext x
    simp [someLeader, noLeader]
  -- the two probabilities add up to the total weight, which is `1`
  have hsplit : prob f (someLeader (k := k)) + prob f (noLeader (k := k)) = 1 := by
    -- rewrite `someLeader` as the complement and `1` as `∑ x, wt f x`
    rw [hcompl, ← sum_wt f]
    unfold prob
    -- merge the two sums into one sum of a pointwise sum
    rw [← sum_add_distrib]
    -- compare term by term
    refine sum_congr rfl fun x _ => ?_
    -- Mathlib: `indicator s f x + indicator sᶜ f x = f x`; our terms are in the other order
    rw [add_comm]
    exact Set.indicator_self_add_compl_apply _ _ _
  -- substitute the value of `prob noLeader` and solve for `prob someLeader`
  rw [prob_noLeader] at hsplit
  linarith

/-- Probability is monotone in the event. -/
lemma prob_mono (hf0 : 0 ≤ f) (hf1 : f ≤ 1) {E F : Set (Fin k → Bool)} (h : E ⊆ F) :
    prob f E ≤ prob f F :=
  -- term by term: the indicator of the smaller set is at most that of the larger, as weights
  -- are non-negative
  sum_le_sum fun x _ => Set.indicator_le_indicator_of_subset h (fun x => wt_nonneg f hf0 hf1 x) x

/-- **T22 is unlikely.** Any event that needs a leader in a window of `k` slots has probability
at most `1 − (1 − f)^k`. By step 1, the event "the attack produces a late certificate RB" needs
a leader in the harm window, so this bounds its probability with `k` the size of that window. -/
theorem prob_le_of_needs_leader (hf0 : 0 ≤ f) (hf1 : f ≤ 1) {E : Set (Fin k → Bool)}
    (hE : ∀ x ∈ E, ∃ j, x j = true) : prob f E ≤ 1 - (1 - f) ^ k := by
  -- the right-hand side is `prob someLeader`
  rw [← prob_someLeader]
  -- and `E ⊆ someLeader` is exactly the hypothesis `hE`
  exact prob_mono f hf0 hf1 hE

/-- With mainnet's `f = 1/20` and a two-slot overshoot, the bound is `39/400 < 1/10`. -/
example : 1 - (1 - (1 / 20 : ℚ)) ^ 2 = 39 / 400 := by norm_num

end Lottery

end Leios
