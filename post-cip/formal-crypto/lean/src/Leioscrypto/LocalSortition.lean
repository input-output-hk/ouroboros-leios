
import Batteries.Data.Rat.Float
import Leioscrypto.BLS


namespace Leioscrypto


private structure ValueWithError where
  value : Rat
  error : Rat

private def absRat (x : Rat) : Rat :=
  if x ≥ 0
  then x
  else - x

instance : HMul Rat ValueWithError ValueWithError where
  hMul
  | x, ⟨ value , error ⟩ => ⟨ x * value , absRat x * error ⟩

private def expTerm (x : Rat) : Nat → Rat
| 0 => 1
| k + 1 => expTerm x k * x / (k + 1)

private def expTaylor (x : Rat) (n : Nat) : ValueWithError :=
  ⟨
    List.sum
      $ List.map (fun k ↦ expTerm x k)
      $ List.range (n + 1)
  , let error := expTerm x (n + 1)
    absRat error
  ⟩

private def poissonTaylor (x : Rat) (k : Nat) (n : Nat) : ValueWithError :=
  -- Exact value of $\sum_{m=0}^k x^m / m!$.
  let a := ValueWithError.value $ expTaylor x k
  -- Taylor approximation of $e^{-x}$.
  let b := expTaylor (- x) n
  -- The $n + 1$ term approximation of the Possion distribution for $k$ events with mean $x$.
  a * b

private partial def trialEstimate (y : Rat) (x : Rat) (k : Nat) (n : Nat) : Ordering :=
  let ⟨ estimate , error ⟩ := poissonTaylor x k n
  if y < estimate - error
  then Ordering.lt
  else if  y > estimate + error
    then Ordering.gt
    else trialEstimate y x k $ n + 1
-- FIXME: The termination proof will require Leibniz's theorem (alternating series estimation theorem).

def comparePoisson (y : Rat) (x : Rat) (k : Nat) : Ordering :=
  -- At least $\lfloor x \rfloor$ terms must be evaluated.
  trialEstimate y x k x.floor.toNat


private def evalSeats (n₂ : Nat) (𝒮 : Rat) (vrf : Rat) : Nat :=
  let x : Rat := n₂ * 𝒮
  let kₘᵢₙ : Int := x.floor

  sorry


def countSeats (n₂ : Nat) (𝒮 : Rat) (σ_eid : BLS.Signature) : Nat :=
  let num : Nat := σ_eid.toByteArray.foldl (fun acc b => (acc <<< 8) + b.toNat) 0
  let den : Nat := 2 ^ 384 - 1
  let vrf : Rat := num.cast / den
  evalSeats n₂ 𝒮 vrf


end Leioscrypto
