import Leios.Base
import Leios.BLS
import Leios.Crypto

open Leios.Base (Party Slot Stake)
open Leios.BLS (KeyGen Signature VerificationKey)
open Leios.Crypto (CryptoHash CryptoHashable)
open Leios.Primitives (Encode Encoding)


namespace Leios.Vote


structure Parameters where
  H : Encoding → Nat
  T : Float → Stake → Nat
  mv : Nat
  kv : Nat


structure ElectionID where
  slot : Slot
  party : Party
deriving Repr, BEq, Hashable

instance : CryptoHashable ElectionID where
  hash
  | ElectionID.mk slot party =>
      CryptoHash.castHash
        $ CryptoHashable.hash
        $ Prod.mk slot party


structure Vote (message : Type) where
  sigmaEid : Signature ElectionID
  sigmaM : Signature message
deriving Repr, BEq, Hashable

instance : CryptoHashable (Vote message) where
  hash
  | Vote.mk sigmaEid sigmaM =>
      CryptoHash.castHash
        $ CryptoHashable.hash
        $ Prod.mk sigmaEid sigmaM


structure Cert (message : Type) where
  votes : List (VerificationKey × Stake × Vote message)
  sigmaEid : Signature ElectionID
  sigmaM : Signature message
deriving Repr, BEq, Hashable

instance : CryptoHashable (Cert message) where
  hash
  | Cert.mk votes sigmaEid sigmaM =>
      CryptoHash.castHash
        $ CryptoHashable.hash
        $ Prod.mk votes
        $ Prod.mk sigmaEid sigmaM


def VoteCount : x → Stake → Nat :=
  sorry


export Leios.BLS (KeyGen)


def GenVote [Encode message] : ElectionId → message → SecretKey → Stake → Vote message :=
  sorry


def VerifyVote [Encode message] : ElectionID → message → VerificationKey → Stake → Vote message → Bool :=
  sorry


def GenCert : ElectionID → message → List (VerificationKey × Stake × Vote message) → Cert message :=
  sorry


def VerifyCert : ElectionId → message → Cert message → Bool :=
  sorry


end Leios.Vote
