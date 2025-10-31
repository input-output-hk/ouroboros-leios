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
Check that a probability is close to unity.
-/
private def nearUnity (x : Float) : Bool := (x - 1).abs < ε

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
        (nearUnity $ (stakeDistribution nPools.value).sum)
      )
    )
  $ group "Quorum" (
      check "All voters vote and all votes are received" (
        ∀ τ : RangedFloat 1 999,
        ∀ committeeSize : RangedNat 100 nPools,
        (nearUnity $ pQuorum 1 committeeSize.value.toFloat τ.value)
      )
    )
  $ group "Conservation of probability" (
      check "Forging RB" (
        ∀ env : Environment,
        ∀ state : State,
        (outcomeNearUnity $ @forgeRb env state)
      )
    $ check "Certifying" (
        ∀ env : Environment,
        ∀ state : State,
        (outcomeNearUnity $ @certify env state)
      )
    $ check "Forging EB" (
        ∀ env : Environment,
        ∀ state : State,
        (outcomeNearUnity $ @forgeEb env state)
      )
    $ check "Voting" (
        ∀ env : Environment,
        ∀ state : State,
        (outcomeNearUnity $ @vote env state)
      )
    )


/--
Testing is done elsewhere in this file.
-/
def main : IO Unit :=
  pure ()
