import Leios.Params
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# One Leios pipeline

This file defines the objects the model talks about; `Leios.Params` holds the protocol
parameters and should be read first. From it we use the vote deadline and the earliest
certificate slot, the Praos delivery bound `Δ` (every honest node can select an RB within `Δ`
slots of its slot) and the EB diffusion time `D` (an EB held by one honest node reaches every
honest node within `D` slots). `Δ` is a property of small blocks that Praos already assumes;
`D` is a property of large blocks that Leios introduces.

A finite set of parties `Fin n` holds non-negative stake summing to one. Some parties are
corrupt; as in Praos, they hold less than half of the stake. A committee (any subset of the
parties) votes on one EB announced at slot `s`.

The adversary's whole power is the function `recv`: the slot at which each party first holds
the complete EB closure and has validated it, with `⊤` for "never". This is the readiness a
committee member needs to vote and a node needs to apply the EB under a certificate (see the
README for what is folded into it). Honest nodes forward what they hold, which the network
axiom `HonestDiffuse` turns into: whatever one honest node holds at slot `t`, every honest
node holds by slot `t + D`.

The only thing we track about Praos is whether an honest node can select the certificate RB,
the later RB carrying the certificate for the EB announced at `s`. Selecting it requires
holding the EB, so a node that obtains the EB later than `Δ` slots after the certificate RB's
slot sees that RB delivered late, and the Praos delivery assumption is broken at that node.
This is the harm behind threat T22.

```
  announcing RB                                                   certificate RB
  (announces the EB)                                              (carries the certificate)
       |                                                                |
       v                                                                v
  -----+-----------+-----------+-----------+ - - - - - - - - - - - - - -+-----------+-----> slots
       s      s+3*Lhdr   s+3*Lhdr+Lvote  s+certGap                      c         c+Delta
       |equivocation|  voting   |   Ldiff  |     c may be any slot      |   Praos   |
       | detection  |  window   |          |     at or after s+certGap  |   bound   |
                                ^                                                   ^
                    honest voters hold the EB                          an honest node still
                    by here (prototype rule)                           without the EB here
                                                                       is harmed (`Harm c`)
```
-/

namespace Leios

open Finset

/-- Everything the adversary and the environment fix for one pipeline. -/
structure World (n : ℕ) where
  /-- Stake of each party. Rational: on the ledger stake is a count of lovelace, and the
  fractions below are ratios of such counts. -/
  stake : Fin n → ℚ
  stake_nonneg : ∀ i, 0 ≤ stake i
  /-- Stake is normalised to `1`, so `τ` and `1/2` are fractions of it. -/
  stake_sum : ∑ i, stake i = 1
  /-- Corrupt parties. -/
  corrupt : Finset (Fin n)
  /-- Honest majority, the Praos assumption. -/
  honest_majority : (∑ i ∈ corrupt, stake i) < 1 / 2
  /-- The voting committee. -/
  committee : Finset (Fin n)
  /-- Slot of the announcing RB. -/
  s : ℕ
  /-- Slot at which each party first holds the validated EB closure; `⊤` if never. -/
  recv : Fin n → ℕ∞
  /-- Corrupt committee members whose votes the adversary contributes. -/
  advVotes : Finset (Fin n)
  advVotes_sub : advVotes ⊆ corrupt ∩ committee

namespace World

variable {n : ℕ} (w : World n) (p : Params)

/-- A party is honest if it is not corrupt. -/
def honest (i : Fin n) : Prop := i ∉ w.corrupt

/-- Total stake of a set of parties. -/
def stakeOf (S : Finset (Fin n)) : ℚ := ∑ i ∈ S, w.stake i

/-- Stake held by the adversary. -/
def advStake : ℚ := w.stakeOf w.corrupt

/-- The adversary cannot reach the quorum on its own: `advStake < 1/2 ≤ τ`. -/
lemma advStake_lt_τ : w.advStake < p.τ :=
  -- chain `advStake < 1/2` (field `honest_majority`) with `1/2 ≤ τ` (field `τ_ge_half`)
  lt_of_lt_of_le w.honest_majority p.τ_ge_half

/-- Last slot at which an honest committee member may obtain the EB and still vote. -/
def voteRecvDeadline : ℕ := w.s + p.voteRecvOffset

/-- Honest committee members that vote: those holding the EB by the vote deadline. -/
def honestVoters : Finset (Fin n) :=
  (w.committee \ w.corrupt).filter fun i => w.recv i ≤ (w.voteRecvDeadline p : ℕ∞)

/-- All voters: honest voters plus the adversary's. -/
def voters : Finset (Fin n) := w.honestVoters p ∪ w.advVotes

/-- A certificate exists when the voters' stake reaches the quorum `τ`. -/
def Certified : Prop := p.τ ≤ w.stakeOf (w.voters p)

/-- Earliest slot of an RB that may carry the certificate. -/
def minCertSlot : ℕ := w.s + p.certGap

/-- Network axiom: if honest `i` holds the EB by slot `t`, then honest `j` holds it by `t + D`.

This is Praos' `Δ`-semi-synchrony ("any message diffused by an honest party during slot `j`
is received by every honest party before the beginning of slot `j + Δ`") applied to the EB
with its own bound `D`. Honest nodes forward every EB they hold, so holding one is as good as
having diffused it. It is the only assumption about the network, and `D` is measured from a
single honest holder, not from a fraction of the stake. -/
def HonestDiffuse : Prop :=
  ∀ i j, w.honest i → w.honest j →
    ∀ t : ℕ, w.recv i ≤ (t : ℕ∞) → w.recv j ≤ ((t + p.D : ℕ) : ℕ∞)

/-- The bad event of threat T22, for a certificate RB in slot `c`.

Praos assumes every RB is selectable by every honest node within `Δ` slots of its slot. A
node can select the certificate RB only once it holds the EB the certificate is about, because
applying the block means applying that EB's transactions. So the certificate RB is effectively
late at honest `j` if `j` obtains the EB after `c + Δ`. That is what T22 tries to bring about:
get the EB certified while most honest nodes still do not have it.

`Harm c` holds when some honest node first holds the EB strictly after slot `c + Δ`; with
`recv j = ⊤` (never) it holds as well, since `⊤` is above every slot. `c` is an argument rather
than fixed to `minCertSlot` because the certificate may be included in any RB at or after
`minCertSlot`, and a later `c` only makes the harm less likely. -/
def Harm (c : ℕ) : Prop := ∃ j, w.honest j ∧ ((c + p.Δ : ℕ) : ℕ∞) < w.recv j

/-!
## Bookkeeping lemmas

Nothing below is about the protocol. These are small facts about sums of stake and about
membership in `honestVoters`, stated once so that proofs about the model can read as the
argument rather than as Finset manipulation. Each statement is a one-line consequence of a
definition, and each proof names the Mathlib lemma that does it.
-/

/-- Stake of any set of parties is non-negative, because every individual stake is. -/
lemma stakeOf_nonneg (S : Finset (Fin n)) : 0 ≤ w.stakeOf S :=
  -- a sum of non-negative terms is non-negative; the term proof is the field `stake_nonneg`
  sum_nonneg fun i _ => w.stake_nonneg i

/-- A larger set of parties holds at least as much stake. For instance `advVotes ⊆ corrupt`
gives `stakeOf advVotes ≤ advStake`. -/
lemma stakeOf_mono {S T : Finset (Fin n)} (h : S ⊆ T) : w.stakeOf S ≤ w.stakeOf T :=
  -- a sum over a subset is at most the sum over the superset when the extra terms are
  -- non-negative
  sum_le_sum_of_subset_of_nonneg h fun i _ _ => w.stake_nonneg i

/-- Stake of a disjoint union is the sum of the stakes. `honestVoters` and `advVotes` are such
a pair, since honest means not corrupt. -/
lemma stakeOf_union_of_disjoint {S T : Finset (Fin n)} (h : Disjoint S T) :
    w.stakeOf (S ∪ T) = w.stakeOf S + w.stakeOf T :=
  -- a sum over a disjoint union splits into two sums
  sum_union h

/-- Unfolding `honestVoters`: a party is an honest voter exactly when it is in the committee,
honest, and holds the EB by the vote deadline. -/
lemma mem_honestVoters {i : Fin n} :
    i ∈ w.honestVoters p ↔
      i ∈ w.committee ∧ w.honest i ∧ w.recv i ≤ (w.voteRecvDeadline p : ℕ∞) := by
  -- unfold `honestVoters` (a `filter` of a set difference) and `honest`; `simp` turns
  -- membership in the filter into a conjunction, and `and_assoc` regroups the brackets
  simp [honestVoters, honest, and_assoc]

/-- An honest voter is honest. -/
lemma honest_of_mem_honestVoters {i : Fin n} (h : i ∈ w.honestVoters p) : w.honest i :=
  -- forward direction of `mem_honestVoters`, second conjunct's first part
  ((w.mem_honestVoters p).1 h).2.1

/-- An honest voter holds the EB by the vote deadline: a vote is evidence of possession, since
an honest node never votes for an EB it has not validated, and cannot validate what it does
not hold. -/
lemma recv_le_of_mem_honestVoters {i : Fin n} (h : i ∈ w.honestVoters p) :
    w.recv i ≤ (w.voteRecvDeadline p : ℕ∞) :=
  -- as above, taking the last conjunct
  ((w.mem_honestVoters p).1 h).2.2

end World

end Leios
