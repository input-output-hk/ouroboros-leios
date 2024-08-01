import Leios.Crypto
import Leios.Primitives

open Leios.Crypto (CryptoHash CryptoHashable)
open Leios.Primitives (ByteString)


namespace Leios.Praos


def Slot := Nat
deriving Repr

instance : HSub Slot Nat Slot where
  hSub s x := Nat.sub s x

instance : CryptoHashable Slot where
  hash := CryptoHash.mk ∘ UInt64.ofNat

namespace Slot

  structure Interval where
    start : Slot
    finish : Slot
  deriving Repr

  def slice (L : Nat) (s : Slot) (x : Nat) : Interval :=
    let s' := Nat.div (s - x * L) L
    {
      start := s'
    , finish := s' + (L - 1)
    }

end Slot


def Tx := ByteString
deriving Repr, CryptoHashable

instance : CryptoHashable Tx where
  hash := CryptoHash.castHash ∘ CryptoHashable.hash


structure Party where
  identifier : Nat
deriving Repr

instance : CryptoHashable Party where
  hash := CryptoHash.mk ∘ UInt64.ofNat ∘ Party.identifier


end Leios.Praos
