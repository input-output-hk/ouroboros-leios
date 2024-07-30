structure ByteString where
  bytes : ByteArray
deriving Inhabited

private def toHexDigit : UInt8 → Char
  |  0 => '0'
  |  1 => '1'
  |  2 => '2'
  |  3 => '3'
  |  4 => '4'
  |  5 => '5'
  |  6 => '6'
  |  7 => '7'
  |  8 => '8'
  |  9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | 15 => 'f'
  |  _ => '?'

private def toHexByte (x : UInt8) : String :=
  let hi := UInt8.div x 16
  let lo := UInt8.mod x 16
  toString (toHexDigit hi) ++ toString (toHexDigit lo)

private def toHexString' (x : ByteArray) : String :=
  let f (bs : String) (b : UInt8) : String := bs ++ toHexByte b
  x.foldl f default

namespace ByteString

  def fromList : List UInt8 → ByteString :=
    mk ∘ ByteArray.mk ∘ Array.mk

  def toList : ByteString → List UInt8
    | mk (ByteArray.mk (Array.mk bs)) => bs

  def toHexString : ByteString → String
    | mk bs => toHexString' bs

  def fromString : String → ByteString :=
    mk ∘ String.toUTF8

end ByteString

instance : ToString ByteString where
  toString x := String.fromUTF8Unchecked x.bytes

instance : Repr ByteString where
  reprPrec x _ := "#" ++ ByteString.toHexString x
