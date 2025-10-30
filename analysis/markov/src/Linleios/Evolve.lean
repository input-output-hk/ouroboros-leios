
import Std.Data.HashMap
import Batteries.Lean.HashMap
import Lean.Data.Json.FromToJson

import Linleios.Types


open Lean (Json)
open Lean.ToJson (toJson)
open Std (HashMap)


/--
Try to forge an RB in this substep, given the state and environment.
-/
def forgeRb {env : Environment} (state : State) : Outcomes :=
  let state' :=
    {
      state with
      clock := state.clock + 1
    }
  let p := 1 - env.fAdversary
  [
    ({state' with hasRb := true, rbCount := state.rbCount + 1}, p)
  , ({state' with hasRb := false, canCertify := false}, 1 - p)
  ]

/--
Try to include a certificate in the latest RB being forged in this substep, given the state and environment.
-/
def certify {env : Environment} (state : State) : Outcomes :=
  if state.hasRb && state.canCertify
    then let p := env.pSpacingOkay
         [
           ⟨{state with ebCount := state.ebCount + 1}, p⟩
         , ⟨state, 1 - p⟩
         ]
    else [(state, 1)]

/--
Try to forge an EB in this substep, given the state and environment.
-/
def forgeEb {env : Environment} (state : State) : Outcomes :=
  if state.hasRb
    then let p := 1 - env.pLate
         [
           ({state with canCertify := true}, p)
         , ({state with canCertify := false}, 1 - p)
         ]
    else [(state, 1)]

/--
Try to vote for an EB in this substep, given the state and environment.
-/
def vote {env : Environment} (state : State) : Outcomes :=
  if state.hasRb
    then let p := env.pQuorum
         [
           (state, p)
         , ({state with canCertify := false}, 1 - p)
         ]
    else [(state, 1)]

/--
Step forward to the next potential block.
-/
def step {env : Environment} : List (State → Outcomes) :=
  [@forgeRb env, @certify env, @forgeEb env, @vote env]


/--
Discard probabilities below the specified threshold.
-/
def prune (ε : Float) : Probabilities → Probabilities :=
  HashMap.filter (fun _ p => p > ε)

/--
Evolve state probabilities on step forward according the a transition function.
-/
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

/--
Chain a sequence of transitions sequentially, evolving probabilities.
-/
def chain (transitions : List (State → Outcomes)) : Probabilities → Probabilities :=
  match transitions with
  | [] => id
  | (t :: ts) => chain ts ∘ evolve t

/--
Simulate the specified number of potential blocks, given a starting set of probabilities.
-/
def simulate (env : Environment) (start : Probabilities) (ε : Float) : Nat → Probabilities
| 0     => start
| n + 1 => let state' := prune ε $ chain (@step env) start
           simulate env state' ε n


/--
Compute the total probabilities of a set of states.
-/
def totalProbability (states : Probabilities) : Probability :=
  states.fold (Function.const State ∘ Add.add) 0

/--
Compute the distribution of EB counts.
-/
def ebDistribution : Probabilities → HashMap Nat Probability :=
  HashMap.fold
    (
      fun acc state p =>
        -- FIXME: Rewrite using `Function.const`.
        HashMap.mergeWith (fun _ => Add.add) acc
          $ singleton ⟨ state.ebCount , p ⟩
    )
    ∅

/--
Format the distribution of EB counts as JSON.
-/
def ebDistributionJson : Probabilities → Json :=
  Json.mkObj
    ∘ List.map (fun ⟨k, v⟩ => ⟨toString k, toJson v⟩)
    ∘ (fun z => z.mergeSort (by exact fun x y => x.fst ≤ y.fst))
    ∘ HashMap.toList
    ∘ ebDistribution

/--
Compute the RB efficiency, given a set of states.
-/
def rbEfficiency (states : Probabilities) : Float :=
  let clock := states.keys.head!.clock
  let rbCount :=
    HashMap.fold
      (fun acc state p =>acc + state.rbCount.toFloat * p)
      0
      states
  rbCount / clock.toFloat

/--
Compute the EB efficiency, given a set of states.
-/
def ebEfficiency (states : Probabilities) : Float :=
  let clock := states.keys.head!.clock
  let ebCount :=
    HashMap.fold
      (fun acc state p =>acc + state.ebCount.toFloat * p)
      0
      states
  ebCount / (clock.toFloat - 1)

/--
Compute the overall efficiency, give a set of states.
-/
def efficiency (states : Probabilities) : Float :=
  let rb := rbEfficiency states
  let eb := ebEfficiency states
  let rbSize := 0.9
  let ebSize := 12.0
  let ρ := ebSize / rbSize
  (rb * (1 - eb) + ρ * eb) / (1 + ρ)
