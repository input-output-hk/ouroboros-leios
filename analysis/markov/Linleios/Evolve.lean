
import Std.Data.HashMap
import Batteries.Lean.HashMap

import Linleios.Types


open Std (HashMap)


def certify {env : Environment} (state : State) : Outcomes :=
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

def vote {env : Environment} (state : State) : Outcomes :=
  [
    (state, env.pQuorum)
  , ({state with canCertify := false}, 1 - env.pQuorum)
  ]

def step {env : Environment} : List (State → Outcomes) :=
  [@certify env, @vote env]


def prune (ε : Float) : Probabilities → Probabilities :=
  HashMap.filter (fun _ p => p > ε)

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

def simulate (env : Environment) (start : Probabilities) (ε : Float) : Nat → Probabilities
| 0     => start
| n + 1 => let state' := prune ε $ chain (@step env) start
           simulate env state' ε n

def totalProbability (states : Probabilities) : Probability :=
  states.values.sum

def ebDistribution : Probabilities → HashMap Nat Probability :=
  HashMap.fold
    (
      fun acc state p =>
        HashMap.mergeWith (fun _ => Add.add) acc
          $ singleton ⟨ state.ebCount , p ⟩
    )
    ∅

def ebEfficiency (states : Probabilities) : Float :=
  let rbCount := states.keys.head!.rbCount
  let ebCount :=
    HashMap.fold
      (fun acc state p =>acc + state.ebCount.toFloat * p)
      0
      states
  ebCount / (rbCount.toFloat - 1)
