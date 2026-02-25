
import Leioscrypto.BLS


/-!
Local sortition in Leios.
-/

namespace Leioscrypto


/-- Track error associated with a rational number. -/
private structure ValueWithError where
  value : Rat
  error : Rat

/-- Absolute value of a rational number. -/
private def absRat (x : Rat) : Rat :=
  if x ≥ 0
  then x
  else - x

/-- Error-aware multiplication of rational numbers. -/
instance : HMul Rat ValueWithError ValueWithError where
  hMul
  | x, ⟨ value , error ⟩ => ⟨ x * value , absRat x * error ⟩

/-- A term in the Taylor expansion of an exponential. -/
private def expTerm (x : Rat) : Nat → Rat
| 0 => 1
| k + 1 => expTerm x k * x / (k + 1)

/-- The Taylor expansion of an exponential. -/
private def expTaylor (x : Rat) (n : Nat) : ValueWithError :=
  ⟨
    List.sum
      $ List.map (fun k ↦ expTerm x k)
      $ List.range (n + 1)
  , let error := expTerm x (n + 1)
    absRat error
  ⟩

/-- Poisson probability using a Taylor expansion. -/
private def poissonTaylor (x : Rat) (k : Nat) (n : Nat) : ValueWithError :=
  -- Exact value of $\sum_{m=0}^k x^m / m!$.
  let a := ValueWithError.value $ expTaylor x k
  -- Taylor approximation of $e^{-x}$.
  let b := expTaylor (- x) n
  -- The $n + 1$ term approximation of the Possion distribution for $k$ events with mean $x$.
  a * b

/-- Determine whether a Taylor expansion for a Possion distribution is sufficiently converged. -/
private partial def trialEstimate (y : Rat) (x : Rat) (k : Nat) (n : Nat) : Ordering :=
  let ⟨ estimate , error ⟩ := poissonTaylor x k n
  if y < estimate - error
    then Ordering.lt
    else if  y > estimate + error
      then Ordering.gt
      else trialEstimate y x k $ n + 1
-- FIXME: The termination proof is equivalent to Leibniz's theorem (the alternating series estimation theorem).

/-- Inverse of the Possion distribution. -/
def comparePoisson (y : Rat) (x : Rat) (k : Nat) : Ordering :=
  -- At least $\lfloor x \rfloor$ terms must be evaluated.
  trialEstimate y x k x.floor.toNat
-- Note that the test suite includes `LSpec` tests for this function.


/-- Determine whether the specified number of voting seats are allowed for a particular VRF value-/
private def allowsSeats (maxSeats : Nat) (vrf : Rat) (x : Rat) (seats : Nat) : Nat :=
  if seats ≥ maxSeats
    then seats
    else if comparePoisson vrf x (seats + 1) == Ordering.lt
      then seats
      else allowsSeats maxSeats vrf x $ seats + 1


/-- Determine the number of seats for a particular VRF value. -/
private def evalSeats (n₂ : Nat) (𝒮 : Rat) (vrf : Rat) : Nat :=
  let x : Rat := (n₂ : Rat) * (𝒮 : Rat)
  if comparePoisson vrf x 0 == Ordering.lt
    then 0
    else allowsSeats n₂ vrf x 0

/-- Count a voter's seats. -/
def countSeats (n₂ : Nat) (𝒮 : Rat) (σ_eid : BLS.Signature) : Nat :=
  let num : Nat := σ_eid.toByteArray.foldl (fun acc b => (acc <<< 8) + b.toNat) 0
  let den : Nat := 2 ^ 384
  let vrf : Rat := num.cast / den
  -- FIXME: We should probably prove `0 ≤ vrf < 1`.
  evalSeats n₂ 𝒮 vrf


end Leioscrypto
