
import Leioscrypto.BLS


namespace Leioscrypto


def evalSeats (n₂ : Nat) (𝒮 : Rat) (vrf : Rat) (h : 0 ≤ vrf ∧ vrf ≤ 1) : Nat :=
  sorry


def countSeats (n₂ : Nat) (𝒮 : Rat) (σ_eid : BLS.Signature) : Nat :=
  let num : Nat := σ_eid.toByteArray.foldl (fun acc b => (acc <<< 8) + b.toNat) 0
  let den : Nat := 2 ^ 384 - 1
  let vrf : Rat := num.cast / den
  let h : 0 ≤ vrf ∧ vrf ≤ 1 :=
    by
      sorry
  evalSeats n₂ 𝒮 vrf h


end Leioscrypto
