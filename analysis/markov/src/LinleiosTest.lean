import Linleios
import LSpec
import Std.Data.HashMap

open LSpec
open Std.HashMap (singleton_eq_insert)


-- Lemmas, in lieu of tests

/--
The genesis state starts with zero counts.
-/
theorem genesis : (default : State).clock = 0 ∧ (default : State).rbCount = 0 ∧ (default : State).ebCount = 0 := by
  constructor
  rfl
  constructor
  rfl
  rfl


-- Generators

structure RangedNat (lo hi : Nat) where
  value: Nat
deriving Repr

instance {lo hi : Nat} : SlimCheck.Shrinkable (RangedNat lo hi) where
  shrink _ := []

instance {lo hi : Nat} : SlimCheck.SampleableExt (RangedNat lo hi) :=
  SlimCheck.SampleableExt.mkSelfContained $
    RangedNat.mk <$> SlimCheck.Gen.choose Nat lo hi

instance : SlimCheck.Random Float where
  randomR lo hi :=
    do
      let res := 1000
      let lo' := (lo * res).ceil.toUInt16.toNat
      let hi' := (hi * res).floor.toUInt16.toNat
      let i ← SlimCheck.Random.randomR lo' hi'
      pure $ i.toFloat / res

structure RangedFloat (lo hi : Float) where
  value: Float
deriving Repr

instance {lo hi : Float} : SlimCheck.Shrinkable (RangedFloat lo hi) where
  shrink _ := []

instance {lo hi : Float} : SlimCheck.SampleableExt (RangedFloat lo hi) :=
  SlimCheck.SampleableExt.mkSelfContained $
    RangedFloat.mk <$> SlimCheck.Gen.choose Float lo hi

instance : SlimCheck.Shrinkable Environment where
  shrink _ := []

instance : SlimCheck.SampleableExt Environment :=
  SlimCheck.SampleableExt.mkSelfContained $
    do
      let Lheader : Nat ← SlimCheck.Gen.choose Nat 1 3
      let Lvote ← SlimCheck.Gen.choose Nat 2 6
      let Ldiff ← SlimCheck.Gen.choose Nat 0 8
      let activeSlotCoefficient : Float ← SlimCheck.Gen.choose Float 0.01 0.05
      let committeeSize ← SlimCheck.Gen.choose Nat 100 800
      let τ ← SlimCheck.Gen.choose Float 0.51 0.99
      let pRbHeaderArrives ← SlimCheck.Gen.choose Float 0.90 1.00
      let pEbValidates ← SlimCheck.Gen.choose Float 0.85 1.00
      let pEbUnvalidated ← SlimCheck.Gen.choose Float 0.00 0.15
      let fAdversary ← SlimCheck.Gen.choose Float 0.00 0.49
      pure $
        makeEnvironment
          Lheader Lvote Ldiff
          activeSlotCoefficient
          committeeSize.toFloat τ
          pRbHeaderArrives pEbValidates pEbUnvalidated
          fAdversary

instance : SlimCheck.Shrinkable State where
  shrink _ := []

instance : SlimCheck.SampleableExt State :=
  SlimCheck.SampleableExt.mkSelfContained $
    do
      let clock ← SlimCheck.Gen.choose Nat 0 1000
      let rbCount ← SlimCheck.Gen.choose Nat 0 clock
      let ebCount ← SlimCheck.Gen.choose Nat 0 rbCount
      let hasRb ← SlimCheck.Gen.chooseAny Bool
      let canCertify ← Bool.and hasRb <$> SlimCheck.Gen.chooseAny Bool
      pure $ State.mk clock rbCount ebCount hasRb canCertify


-- Property-based tests.

/--
Tolerance for floating-point operations.
-/
private def ε := 1e-6

/--
Check that a probability is near a specified value.
-/
private def nearValue (value x : Float) : Bool := (x - value).abs < ε

/--
Check that a probability is close to unity.
-/
private def nearUnity : Float → Bool := nearValue 1

/--
Check that the total outcome is near unity.
-/
private def outcomeNearUnity (os : Outcomes) : Bool :=
  nearUnity $  os.foldl (fun acc sp ↦ acc + sp.snd) 0

#lspec
    group "Probabilities" (
      test "Initial probability is unity" (
        totalProbability (default : Probabilities) == 1
      )
    )
  $ group "Stake distribution" (
      check "Stake fractions are positive" (
        ∀ nPools : RangedNat 500 5000,
        ((stakeDistribution nPools.value).map (fun x ↦ decide $ x > 0)).and
      )
    $ check "Stake fractions sum to unity" (
        ∀ nPools : RangedNat 500 5000,
        nearUnity $ (stakeDistribution nPools.value).sum
      )
    )
  $ group "Quorum" (
      check "All voters vote and all votes are received" (
        ∀ τ : RangedFloat 0.51 0.76,
        ∀ committeeSize : RangedNat 700 1000,
        nearUnity $ pQuorum 1 committeeSize.value.toFloat τ.value
      )
    )
  $ group "Conservation of probability" (
      check "Forging RB" (
        ∀ env : Environment,
        ∀ state : State,
        outcomeNearUnity $ @forgeRb env state
      )
    $ check "Certifying" (
        ∀ env : Environment,
        ∀ state : State,
        outcomeNearUnity $ @certify env state
      )
    $ check "Forging EB" (
        ∀ env : Environment,
        ∀ state : State,
        outcomeNearUnity $ @forgeEb env state
      )
    $ check "Voting" (
        ∀ env : Environment,
        ∀ state : State,
        outcomeNearUnity $ @vote env state
      )
    $ check "Simulation" (
        ∀ env : Environment,
        ∀ steps : RangedNat 0 30,
        nearUnity ∘ totalProbability $ simulate env default 0 steps.value
      )
    )
  $ group "EB distribution" (
      check "Total probability is unity" (
        ∀ env : Environment,
        ∀ steps : RangedNat 0 30,
        let states := simulate env default 0 steps.value
        let ebDist := ebDistribution states
        nearUnity $ ebDist.values.sum
      )
    )
  $ group "Efficiency" (
      group "RB efficiency" (
        check "Honest environment" (
          ∀ steps : RangedNat 1 30,
          let states := simulate default default 0 steps.value
          nearUnity $ rbEfficiency states
        )
      $ check "Adversarial environment" (
          ∀ fAdversary : RangedFloat 0.01 0.49,
          let env := {(default : Environment) with fAdversary := fAdversary.value}
          let states := simulate env default 0 30
          nearValue (1 - fAdversary.value) $ rbEfficiency states
        )
      )
    $ group "EB efficiency" (
        check "Ideal environment" (
          let states := simulate default default 0 30
          nearValue (0.95^13) $ ebEfficiency states
        )
      $ check "Quorum failure" (
          ∀ τ : RangedFloat 0.90 1.00,
          let env := makeEnvironment 1 4 7 0.05 600 τ.value 1 1 0 0
          let states := simulate env default 0 30
          nearValue (0.95^13 * env.pQuorum) $ ebEfficiency states
        )
      $ check "Late EB validation" (
          ∀ pLate : RangedFloat 0.01 0.99,
          let env := {(default : Environment) with pLate := pLate.value}
          let states := simulate env default 0 30
          nearValue (0.95^13 * (1 - pLate.value)) $ ebEfficiency states
        )
      $ check "Adversarial environment" (
          ∀ fAdversary : RangedFloat 0.01 0.49,
          let env := {(default : Environment) with fAdversary := fAdversary.value}
          let states := simulate env default 0 30
          nearValue (0.95^13 * (1 - fAdversary.value)^2) $ ebEfficiency states
        )
      )
    )


/--
Testing is done elsewhere in this file.
-/
def main : IO Unit :=
  pure ()
