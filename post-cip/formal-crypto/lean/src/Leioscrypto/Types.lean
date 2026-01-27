
import Std.Data.HashMap

open Std (HashMap)


namespace Leioscrypto


def PraosNonce := BitVec 256
  deriving Repr


def BlockHash := BitVec 256
  deriving Repr


def Coin := Rat
  deriving Repr, OfNat, LT, LE


def Slot := Nat
  deriving Repr, LE


end Leioscrypto
