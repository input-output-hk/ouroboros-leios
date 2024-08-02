import Lean.Data
import Leios.Crypto

open Lean (HashSet)
open Leios.Crypto (CryptoHash CryptoHashable)


namespace Leios.BLS


structure Param where
deriving Repr


structure SecretKey where
deriving Repr


structure VerificationKey where
deriving Repr, BEq, Hashable

instance : CryptoHashable VerificationKey where
  hash _ := CryptoHash.mk 0


structure Proof where
deriving Repr

instance : CryptoHashable Proof where
  hash _ := CryptoHash.mk 0


structure Signature (message : Type) where
  bytes : UInt64  -- FIXME: Replace with a fixed-length bytestring.
deriving Repr

instance : BEq (Signature message) where
  beq x y := BEq.beq x.bytes y.bytes

instance : Hashable (Signature message) where
  hash := Hashable.hash ∘ Signature.bytes

instance : CryptoHashable (Signature message) where
  hash := CryptoHash.mk ∘ Signature.bytes


def KeyGen : Param → SecretKey × VerificationKey × Proof :=
  sorry


def Check : VerificationKey → Proof → Bool :=
  sorry


def Sign : SecretKey → message → Signature message :=
  sorry


def Ver : VerificationKey → message → Signature message → Bool :=
  sorry


def AKey : HashSet VerificationKey → VerificationKey :=
  sorry


def ASig : HashSet (Signature message) → Signature message :=
  sorry


def BKey : HashSet VerificationKey → HashSet (Signature message) → VerificationKey :=
  sorry


def BSig : HashSet (Signature message) → Signature message :=
  sorry


end Leios.BLS
