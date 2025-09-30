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

def makeEnvironment (activeSlotCoefficient pRbHeaderArrives pEbValidates committeeSize τ : Float) (Lheader Lvote Ldiff : Nat) : Environment :=
  {
    activeSlotCoefficient := activeSlotCoefficient
    Lheader := Lheader
    Lvote := Lvote
    Ldiff := Ldiff
    pSpacingOkay := (1 - activeSlotCoefficient).pow (3 * Lheader + Lvote + Ldiff - 1).toFloat
    pQuorum := pQuorum (pRbHeaderArrives * pEbValidates) committeeSize τ
  }


structure State where
  rbCount : Nat
  ebCount : Nat
  canCertify : Bool
deriving Repr, BEq, Hashable, Inhabited

theorem genesis : (default : State).rbCount = 0 ∧ (default : State).ebCount = 0 := by
  constructor
  rfl
  rfl


def Probabilities := HashMap State Probability
deriving Repr, EmptyCollection

instance : Inhabited Probabilities where
  default := (∅ : Probabilities).insert Inhabited.default 1


abbrev Outcomes := List (State × Probability)
