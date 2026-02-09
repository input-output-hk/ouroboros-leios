
import Batteries.Data.Rat.Float
import LSpec
import Leioscrypto
import Mathlib.Data.Nat.Factorial.Basic

open LSpec
open Leioscrypto (comparePoisson)


/-!
Property-based tests for Leios cryptography.
-/

-- Property-based tests are provided here for the rational representation of the Poisson distribution because theorems were not proved for it.
section

structure TestCase where
  x : Rat
  y : Rat
  k : Nat
deriving Repr

instance : SlimCheck.Shrinkable TestCase where
  shrink _ := []

instance : SlimCheck.SampleableExt TestCase :=
  SlimCheck.SampleableExt.mkSelfContained $
    do
      let den' : Nat := 1000000000
      let den : Rat := den'
      let x : Rat ← SlimCheck.Gen.choose Nat 0 den'
      let y : Rat ← SlimCheck.Gen.choose Nat 0 den'
      let k : Nat ← SlimCheck.Gen.choose Nat 0 15
      pure ⟨ x / den , y / den , k⟩

def poisson (x : Float) (k : Nat) : Float :=
  let a := Float.exp (- x)
  let bs :=
    (List.range (k + 1)).map
      $ fun n ↦ x.pow n.toFloat / n.factorial.toFloat
  a * bs.sum

#lspec
  check "Poisson comparison" (
    ∀ tc : TestCase
  , let actual := Float.decLt tc.y.toFloat $ poisson tc.x tc.k
    let expected := comparePoisson tc.y tc.x tc.k = Ordering.lt
    expected == actual.decide
  )

end


/--
Testing is done elsewhere in this file, via `Lspec`.
-/
def main : IO Unit :=
  pure ()
