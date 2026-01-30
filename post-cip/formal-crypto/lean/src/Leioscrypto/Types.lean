
namespace Leioscrypto


private def uint64toByteArray (n : UInt64) : ByteArray :=
  let b0 := n.toUInt8
  let b1 := (n >>> 8).toUInt8
  let b2 := (n >>> 16).toUInt8
  let b3 := (n >>> 24).toUInt8
  let b4 := (n >>> 32).toUInt8
  let b5 := (n >>> 40).toUInt8
  let b6 := (n >>> 48).toUInt8
  let b7 := (n >>> 56).toUInt8
  ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7]


def Slot := UInt64
deriving LE

def Slot.toByteArray : Slot → ByteArray :=
  uint64toByteArray


def Coin := Rat
deriving OfNat, LT, LE


def PraosNonce := Vector UInt8 32

def PraosNonce.toByteArray : PraosNonce → ByteArray :=
  ByteArray.mk ∘ Vector.toArray


def BlockHash := Vector UInt8 32

def BlockHash.toByteArray : BlockHash → ByteArray :=
  ByteArray.mk ∘ Vector.toArray


def PoolKeyHash := BitVec 224
 deriving BEq, LawfulBEq


def ColdKeySignature := BitVec 256
deriving BEq


def PoolIndex := Nat
deriving LT


def ElectionId := UInt64

def ElectionId.toByteArray : ElectionId → ByteArray :=
  uint64toByteArray


end Leioscrypto
