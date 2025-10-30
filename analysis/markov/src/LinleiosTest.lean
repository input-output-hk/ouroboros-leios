import Linleios
import Std.Data.HashMap

open Std.HashMap (singleton_eq_insert)


/--
The genesis state starts with zero counts.
-/
theorem genesis : (default : State).clock = 0 ∧ (default : State).rbCount = 0 ∧ (default : State).ebCount = 0 := by
  constructor
  rfl
  constructor
  rfl
  rfl

/-
The initial probability is unity.
-/
#guard totalProbability (default : Probabilities) == 1


def main : IO Unit :=
  pure ()
