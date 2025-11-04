import Std.Data.HashMap
import Batteries.Lean.HashMap

import Linleios.Probability


open Std (HashMap)


/--
Represent probabilities as floating-point numbers.
-/
abbrev Probability := Float

/--
The constant parameters used for computing transitions.
-/
structure Environment where
  /-- The active slot coefficient. -/
  activeSlotCoefficient : Probability
  /-- The $L_\text{hdr}$ protocol parameter. -/
  Lheader : Nat
  /-- The $L_\text{vote}$ protocol parameter. -/
  Lvote : Nat
  /-- The $L_\text{diff}$ protocol parameter. -/
  Ldiff : Nat
  /-- The probability that an RB occurs long enough after the previous RB so that an EB can be certified. -/
  pSpacingOkay : Probability
  /-- The per-step quorum probability. -/
  pQuorum : Probability
  /-- The probability that the EB and transaction data arrives too late to compute the ledger. -/
  pLate : Probability
  /-- The fraction of adversarial stake. -/
  fAdversary : Float
deriving Repr

/--
Create an environment.

- `activeSlotCoefficient`: the active slot coefficient
- `committeeSize`: the mean committee size
- `τ`: the quorum fraction
- `pRbHeaderArrives`: the probability that an RB header arrives before $L_\text{hdr}$ slots
- `pEBValidates`: the probability that an EB is validated before $3 L_\text{hdr} + L_\text{vote} + L_\text{diff}$ slots
- `pEbUnvalidated`: the probability that the EB and transaction data arrives too late to compute the ledger
- `fAdversary`: the fraction of adversarial stake
-/
def makeEnvironment (Lheader Lvote Ldiff : Nat) (activeSlotCoefficient committeeSize τ pRbHeaderArrives pEbValidates pEbUnvalidated fAdversary : Float) : Environment :=
  {
    activeSlotCoefficient := activeSlotCoefficient
    Lheader := Lheader
    Lvote := Lvote
    Ldiff := Ldiff
    pSpacingOkay := (1 - activeSlotCoefficient).pow (3 * Lheader + Lvote + Ldiff - 1).toFloat
    pQuorum := pQuorum (pRbHeaderArrives * pEbValidates * (1 - fAdversary)) committeeSize τ
    pLate := pEbUnvalidated * (1 - committeeSize / nPools.toFloat)
    fAdversary := fAdversary
  }

/--
A perfect honest environment with the recommended protocol parameters.
-/
instance : Inhabited Environment where
  default := makeEnvironment 1 4 7 0.05 700 0.75 1 1 0 0


/--
The state of the chain's evolution.
-/
structure State where
  /-- The number of potential RB oppurtunities. -/
  clock : Nat
  /-- The number of RBs actually forged. -/
  rbCount : Nat
  /-- The number of EBs certified. -/
  ebCount : Nat
  /-- Whether an RB was forged in the current step. -/
  hasRb : Bool
  /-- Whether an EB could be certified in the current step. -/
  canCertify : Bool
deriving Repr, BEq, Hashable, Inhabited

/--
The active states and their probabilities.
-/
def Probabilities := HashMap State Probability
deriving Repr, EmptyCollection

instance : Inhabited Probabilities where
  -- TODO: Rewrite using `Singleton.singleton`.
  default := (∅ : Probabilities).insert Inhabited.default 1


/--
An outcome is a list of new states and their probabilities. -/
abbrev Outcomes := List (State × Probability)
