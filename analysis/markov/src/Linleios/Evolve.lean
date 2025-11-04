
import Std.Data.HashMap

import Linleios.Types


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
