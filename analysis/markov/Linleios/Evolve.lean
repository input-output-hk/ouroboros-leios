
import Std.Data.HashMap
import Batteries.Lean.HashMap

open Std (HashMap)


abbrev Probability := Float


structure Environment where
  activeSlotCoefficient : Probability
  Lheader : Nat
  Lvote : Nat
  Ldiff : Nat
  pSpacingOkay : Probability

def makeEnvironment (activeSlotCoefficient : Float) (Lheader Lvote Ldiff : Nat) : Environment :=
  {
    activeSlotCoefficient := activeSlotCoefficient
    Lheader := Lheader
    Lvote := Lvote
    Ldiff := Ldiff
    pSpacingOkay := (1 - activeSlotCoefficient).pow (3 * Lheader + Lvote + Ldiff - 1).toFloat
  }


structure State where
  rbCount : Nat
  ebCount : Nat
deriving Repr, BEq, Hashable, Inhabited

example : (default : State).rbCount = 0 := rfl

example : (default : State).ebCount = 0 := rfl


def Probabilities := HashMap State Probability
deriving Repr, EmptyCollection

instance : Inhabited Probabilities where
  default := (∅ : Probabilities).insert Inhabited.default 1


def forge {env : Environment} (state : State) : List (State × Probability) :=
  [
    ⟨
      {
        state with
        rbCount := state.rbCount + 1
      }
    , env.pSpacingOkay
    ⟩
  , ⟨
      {
        state with
        rbCount := state.rbCount + 1
        ebCount := state.ebCount + 1
      }
    , env.pSpacingOkay
    ⟩
  ]


def evolve (transition : State → List (State × Probability)) : Probabilities → Probabilities :=
  HashMap.fold
    (
      fun acc state p =>
        HashMap.mergeWith (fun _ => Add.add) acc
          ∘ HashMap.map (fun _ => Mul.mul p ∘ List.sum ∘ List.map Prod.snd)
          ∘ List.groupByKey Prod.fst
          $ transition state
    )
    ∅
