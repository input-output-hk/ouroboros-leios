
import Std.Data.HashMap
import Batteries.Lean.HashMap

open Std (HashMap)


private partial def erf (x : Float) : Float :=
  if x < 0
    then - erf (- x)
    else
      let p := 0.3275911
      let a₁ := 0.254829592
      let a₂ := -0.284496736
      let a₃ := 1.421413741
      let a₄ := -1.453152027
      let a₅ := 1.061405429
      let t := 1 / (1 + p * x)
      1 - (a₁ * t + a₂ * t^2 + a₃ * t^3 + a₄ * t^4 + a₅ * t^5) * Float.exp (- x^2)

private def cdfGaussian (x μ σ : Float) : Float :=
  (1 + erf ((x - μ) / σ / Float.sqrt 2)) / 2

private def bisectionSearch (f : Float → Float) (low high : Float) (ε : Float) (maxIter : Nat) : Float :=
  match maxIter with
  | 0 => (low + high) / 2
  | maxIter' + 1 =>
    let mid := (low + high) / 2
    let fmid := f mid
    if high - low < ε || Float.abs fmid < ε then
      mid
    else if f low * fmid < 0 then
      bisectionSearch f low mid ε maxIter'
    else
      bisectionSearch f mid high ε maxIter'
termination_by maxIter


abbrev Probability := Float


def nPools : Nat := 2500

def stakeDistribution (nPools : Nat) : List Float :=
  (List.range nPools).map (fun k => ((k + 1).toFloat / nPools.toFloat)^10 - (k.toFloat / nPools.toFloat)^10)

private def calibrateCommittee(committeeSize : Float) : Float :=
  let stakes : List Float := stakeDistribution nPools
  let f (m : Float) : Float :=
    let ps : List Float := stakes.map (fun s => 1 - Float.exp (- m * s))
    ps.sum - committeeSize
  bisectionSearch f committeeSize nPools.toFloat 0.5 10

private def committeeDistribution (pSuccessfulVote committeeSize : Float) : Float × Float :=
  let stakes : List Float := stakeDistribution nPools
  let m := calibrateCommittee committeeSize
  let ps : List Float := stakes.map (fun s => pSuccessfulVote * (1 - Float.exp (- m * s)))
  let μ := ps.sum
  let σ := (ps.map (fun p => p * (1 - p))).sum.sqrt
  ⟨ μ , σ ⟩

def pQuorum (pSuccessfulVote committeeSize τ : Float) : Float :=
  let ⟨ μ , σ ⟩ := committeeDistribution pSuccessfulVote committeeSize
  1 - cdfGaussian (τ * committeeSize) μ σ

#eval pQuorum 0.90 600 0.75


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
