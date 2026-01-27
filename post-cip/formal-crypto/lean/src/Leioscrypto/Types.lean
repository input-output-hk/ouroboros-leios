
namespace Leioscrypto


def Slot := Nat
  deriving Repr, LE


def Coin := Rat
  deriving Repr, OfNat, LT, LE


def PraosNonce := BitVec 256
  deriving Repr


def BlockHash := BitVec 256
  deriving Repr


def PoolKeyHash := BitVec 224
  deriving Repr, BEq


def ColdKeySignature := BitVec 256
  deriving Repr, BEq


end Leioscrypto
