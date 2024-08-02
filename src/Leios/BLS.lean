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


structure Proof where
deriving Repr


structure Signature where
  bytes : UInt64  -- FIXME: Replace with a fixed-length bytestring.
deriving Repr, BEq, Hashable

instance : CryptoHashable Signature where
  hash := CryptoHash.mk ∘ Signature.bytes


def KeyGen : Param → SecretKey × VerificationKey × Proof :=
  sorry


def Check : VerificationKey → Proof → Bool :=
  sorry


def Sign : SecretKey → message → Signature :=
  sorry


def Ver : VerificationKey → message → Signature → Bool :=
  sorry


def AKey : HashSet VerificationKey → VerificationKey :=
  sorry


def ASig : HashSet Signature → Signature :=
  sorry


def BKey : HashSet VerificationKey → HashSet Signature → VerificationKey :=
  sorry


def BSig : HashSet Signature → Signature :=
  sorry


end Leios.BLS
