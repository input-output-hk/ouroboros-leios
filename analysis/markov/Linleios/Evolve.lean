
import Std.Data.HashMap
import Batteries.Lean.HashMap

open Std (HashMap)


abbrev Probability := Float


def approxCommittee (committeeSize : Float) : Float × Float :=
  let nPools : Nat := 2500
  let stakes : List Float := (List.range nPools).map (fun k => ((k + 1).toFloat / nPools.toFloat)^10 - (k.toFloat / nPools.toFloat)^10)
  let ps : List Float := stakes.map (fun s => 1 - Float.exp (- committeeSize * s))
  let μ : Float := ps.sum
  let σ := (ps.map (fun p => p * (1 - p))).sum.sqrt
  ⟨ μ , σ ⟩


structure Environment where
  activeSlotCoefficient : Probability
  Lheader : Nat
  Lvote : Nat
  Ldiff : Nat
  pSpacingOkay : Probability
  pRbHeaderArrives : Probability
  pEbValidates : Probability

def makeEnvironment (activeSlotCoefficient pRbHeaderArrives pEbValidates : Float) (Lheader Lvote Ldiff : Nat) : Environment :=
  {
    activeSlotCoefficient := activeSlotCoefficient
    Lheader := Lheader
    Lvote := Lvote
    Ldiff := Ldiff
    pSpacingOkay := (1 - activeSlotCoefficient).pow (3 * Lheader + Lvote + Ldiff - 1).toFloat
    pRbHeaderArrives := pRbHeaderArrives
    pEbValidates := pEbValidates
  }


structure State where
  rbCount : Nat
  ebCount : Nat
  canCertify : Bool
deriving Repr, BEq, Hashable, Inhabited

example : (default : State).rbCount = 0 := rfl

example : (default : State).ebCount = 0 := rfl


def Probabilities := HashMap State Probability
deriving Repr, EmptyCollection

instance : Inhabited Probabilities where
  default := (∅ : Probabilities).insert Inhabited.default 1


abbrev Outcomes := List (State × Probability)


def forge {env : Environment} (state : State) : Outcomes :=
  let state' :=
    {
      state with
      rbCount := state.rbCount + 1
      canCertify := true
    }
  if state.canCertify
    then [
           ⟨{state' with ebCount := state.ebCount + 1}, env.pSpacingOkay⟩
         , ⟨state', 1 - env.pSpacingOkay⟩
         ]
    else [(state', 1)]

def validate {env : Environment} (state : State) : Outcomes :=
  [
    (state, env.pRbHeaderArrives * env.pEbValidates)
  , ({state with canCertify := false}, 1 - env.pRbHeaderArrives * env.pEbValidates)
  ]

def step {env : Environment} : List (State → Outcomes) :=
  [@forge env, @validate env]


def evolve (transition : State → Outcomes) : Probabilities → Probabilities :=
  HashMap.fold
    (
      fun acc state p =>
        HashMap.mergeWith (fun _ => Add.add) acc
          ∘ HashMap.map (fun _ => Mul.mul p ∘ List.sum ∘ List.map Prod.snd)
          ∘ List.groupByKey Prod.fst
          $ transition state
    )
    ∅

def chain (transitions : List (State → Outcomes)) : Probabilities → Probabilities :=
  match transitions with
  | [] => id
  | (t :: ts) => chain ts ∘ evolve t

def simulate (env : Environment) (start : Probabilities) : Nat → Probabilities
| 0     => start
| n + 1 => let state' := chain (@step env) start
           simulate env state' n

def prune (ε : Float) : Probabilities → Probabilities :=
  HashMap.filter (fun _ p => p > ε)

def totalProbability (states : Probabilities) : Probability :=
  states.values.sum
