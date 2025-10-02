import Std.Data.HashMap
import Batteries.Lean.HashMap

import Linleios.Probability


open Std (HashMap)


abbrev Probability := Float


structure Environment where
  activeSlotCoefficient : Probability
  Lheader : Nat
  Lvote : Nat
  Ldiff : Nat
  pSpacingOkay : Probability
  pQuorum : Probability
  pLate : Probability
  fAdversary : Float
deriving Repr

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


structure State where
  clock : Nat
  rbCount : Nat
  ebCount : Nat
  hasRb : Bool
  canCertify : Bool
deriving Repr, BEq, Hashable, Inhabited

theorem genesis : (default : State).clock = 0 ∧ (default : State).rbCount = 0 ∧ (default : State).ebCount = 0 := by
  constructor
  rfl
  constructor
  rfl
  rfl


def Probabilities := HashMap State Probability
deriving Repr, EmptyCollection

instance : Inhabited Probabilities where
  default := (∅ : Probabilities).insert Inhabited.default 1


abbrev Outcomes := List (State × Probability)
