import Std.Data.HashMap
import Batteries.Lean.HashMap
import Lean.Data.Json.FromToJson

import Linleios.Types

import Linleios.Probability
import Linleios.Evolve

open Lean (Json)
open Lean.ToJson (toJson)
open Std (HashMap)


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


#eval ebEfficiency (simulate {(default : Environment) with pLate := 0.1} default 0 30)
#eval (0.95^13 * 0.9)

#eval makeEnvironment 1 4 7 0.05 600 0.75 1 1 0 0.1
#eval ebEfficiency (simulate (makeEnvironment 1 4 7 0.05 600 0.75 1 1 0 0.1) default 0 30)
#eval (0.95^13 * 0.9)
