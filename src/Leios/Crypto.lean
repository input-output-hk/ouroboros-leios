import Leios.Primitives

open Leios.Primitives (ByteString)


namespace Leios.Crypto


structure CryptoHash (a : Type) where
  bytes : UInt64  -- FIXME: Replace with a fixed-length bytestring.
deriving Repr

namespace CryptoHash

  def castHash : CryptoHash a → CryptoHash b := CryptoHash.mk ∘ CryptoHash.bytes

end CryptoHash


class CryptoHashable (a : Type) where
  hash : a → CryptoHash a

instance : CryptoHashable (CryptoHash a) where
  hash := CryptoHash.castHash

instance : CryptoHashable Unit where
  hash _ := CryptoHash.mk 0

instance [CryptoHashable a] [CryptoHashable b] : CryptoHashable (a × b) where
  hash t :=
    let hx := CryptoHash.bytes $ CryptoHashable.hash t.fst
    let hy := CryptoHash.bytes $ CryptoHashable.hash t.snd
    CryptoHash.mk $ UInt64.xor hx hy

instance [CryptoHashable a] [CryptoHashable b] [CryptoHashable c] : CryptoHashable (a × b × c) where
  hash t :=
    let hx := CryptoHash.bytes $ CryptoHashable.hash t.fst
    let hy := CryptoHash.bytes $ CryptoHashable.hash t.snd
    CryptoHash.mk $ UInt64.xor hx hy

instance [CryptoHashable a] [CryptoHashable b] [CryptoHashable c] [CryptoHashable d] : CryptoHashable (a × b × c × d) where
  hash t :=
    let hx := CryptoHash.bytes $ CryptoHashable.hash t.fst
    let hy := CryptoHash.bytes $ CryptoHashable.hash t.snd
    CryptoHash.mk $ UInt64.xor hx hy

instance [CryptoHashable a] [CryptoHashable b] [CryptoHashable c] [CryptoHashable d] [CryptoHashable e] : CryptoHashable (a × b × c × d × e) where
  hash t :=
    let hx := CryptoHash.bytes $ CryptoHashable.hash t.fst
    let hy := CryptoHash.bytes $ CryptoHashable.hash t.snd
    CryptoHash.mk $ UInt64.xor hx hy

instance [CryptoHashable a] : CryptoHashable (List a) where
  hash :=
    let f h := UInt64.xor h ∘ CryptoHash.bytes ∘ CryptoHashable.hash
    CryptoHash.mk ∘ List.foldl f 0

instance : CryptoHashable ByteString where
  hash := CryptoHash.mk ∘ ByteArray.hash ∘ ByteString.bytes


structure Signature where
  bytes : UInt64  -- FIXME: Replace with a fixed-length bytestring.
deriving Repr

instance : CryptoHashable Signature where
  hash := CryptoHash.mk ∘ Signature.bytes


structure LotteryProof where
deriving Repr

instance : CryptoHashable LotteryProof where
  hash _ := CryptoHash.mk 0


end Leios.Crypto
