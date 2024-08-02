import Lean.Data
import Leios.Crypto
import Leios.Primitives

open Lean (HashSet)
open Leios.Crypto (CryptoHash CryptoHashable)
open Leios.Primitives (ByteString)


namespace Leios.Base


def Slot := Nat
deriving Repr, BEq, Hashable

instance : HSub Slot Nat Slot where
  hSub s x := Nat.sub s x

instance : CryptoHashable Slot where
  hash := CryptoHash.mk ∘ UInt64.ofNat

namespace Slot

  structure Interval where
    start : Slot
    finish : Slot
  deriving Repr, Hashable

  def slice (L : Nat) (s : Slot) (x : Nat) : Interval :=
    let s' := Nat.div (s - x * L) L
    {
      start := s'
    , finish := s' + (L - 1)
    }

end Slot


def Tx := ByteString
deriving Repr, BEq, Hashable, CryptoHashable

instance : CryptoHashable Tx where
  hash := CryptoHash.castHash ∘ CryptoHashable.hash


structure Party where
  identifier : Nat
deriving Repr, BEq, Hashable

instance : CryptoHashable Party where
  hash := CryptoHash.mk ∘ UInt64.ofNat ∘ Party.identifier


def Parties := HashSet Party

/-
instance : Repr Parties where
  reprPrec := Repr.reprPrec ∘ HashSet.toList
-/

instance : BEq Parties where
  beq x y := BEq.beq x.toList y.toList

instance : Hashable Parties where
  hash := Hashable.hash ∘ HashSet.toList


def Stake := Nat
deriving Repr, BEq, Hashable

instance : CryptoHashable Stake where
  hash := CryptoHash.mk ∘ UInt64.ofNat


end Leios.Base
