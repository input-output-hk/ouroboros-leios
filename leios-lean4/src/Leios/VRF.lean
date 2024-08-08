import Lean.Data
import Leios.Base
import Leios.Crypto

open Lean (HashMap HashSet)
open Leios.Base (Party)
open Leios.Crypto (CryptoHash CryptoHashable)

namespace Leios.VRF


structure PublicKey where
deriving Repr, BEq, Hashable


structure DomainValue where
deriving Repr, BEq, Hashable


structure RangeValue where
deriving Repr, BEq, Hashable


structure Proof where
deriving Repr, BEq, Hashable

instance : CryptoHashable Proof where
  hash _ := CryptoHash.mk 0


structure Variables where
  Keys : HashMap Party (HashSet PublicKey)
  T : HashMap (PublicKey × DomainValue) (RangeValue × HashSet Proof)
  E : HashSet (PublicKey × DomainValue × RangeValue)
deriving Inhabited


class Simulator (S : Type) where
  GetKey : S → Party → PublicKey
  Eval : S → PublicKey → DomainValue → Proof
  Verify : S → PublicKey → DomainValue → RangeValue → Proof → Bool


def GetKey [Simulator S] [MonadStateOf Variables m] : S → Party → m PublicKey :=
  sorry


def RegKey [Simulator S] [MonadStateOf Variables m] : S → Party → PublicKey → m Unit :=
  sorry


def Eval [Simulator S] [MonadStateOf Variables m] : S → Party → PublicKey → DomainValue → m (RangeValue × Proof) :=
  sorry


def Verify [Simulator S] [MonadReaderOf Variables m] : S → PublicKey → DomainValue → RangeValue → Proof → m Bool :=
  sorry


def Leak [Functor m] [MonadReaderOf Variables m] : m (HashSet (PublicKey × DomainValue × RangeValue)) :=
  Functor.map Variables.E $ MonadReaderOf.read


end Leios.VRF
