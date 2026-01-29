
namespace Leioscrypto


def Slot := Nat
  deriving Repr, LE


def Coin := Rat
  deriving OfNat, LT, LE


def PraosNonce := BitVec 256


def BlockHash := BitVec 256


def PoolKeyHash := BitVec 224
  deriving BEq, LawfulBEq


def ColdKeySignature := BitVec 256
  deriving BEq


def PoolIndex := Nat


def ElectionId := Nat


end Leioscrypto
