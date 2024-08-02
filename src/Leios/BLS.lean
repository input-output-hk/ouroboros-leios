import Lean.Data
import Leios.Crypto
import Leios.Primitives

open Lean (HashSet)
open Leios.Crypto (CryptoHash CryptoHashable)
open Leios.Primitives (Encode)


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
  bytes : Nat
deriving Repr, BEq, Hashable

instance : BEq (Signature message) where
  beq x y := BEq.beq x.bytes y.bytes

instance : Hashable (Signature message) where
  hash := Hashable.hash ∘ Signature.bytes

instance : CryptoHashable (Signature message) where
  hash := CryptoHash.mk ∘ Hashable.hash ∘ Signature.bytes


def KeyGen : Param → SecretKey × VerificationKey × Proof :=
  sorry


def Check : VerificationKey → Proof → Bool :=
  sorry


def Sign [Encode message] : SecretKey → message → Signature message :=
  sorry


def Ver [Encode message] : VerificationKey → message → Signature message → Bool :=
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
