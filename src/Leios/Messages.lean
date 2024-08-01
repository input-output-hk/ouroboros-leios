import Leios.Crypto
import Leios.Praos
import Leios.Primitives

open Leios.Crypto (CryptoHash CryptoHashable LotteryProof Signature)
open Leios.Praos
open Leios.Primitives


namespace Leios.Messages


structure Body where
  txs : List Tx
deriving Repr

instance : CryptoHashable Body where
  hash := CryptoHash.castHash ∘ CryptoHashable.hash ∘ Body.txs


structure Header where
  slot : Slot
  party : Party
  proof : LotteryProof
  bodyHash : CryptoHash Body
  signature : Signature
deriving Repr

instance : CryptoHashable Header where
  hash
  | Header.mk slot party proof bodyHash signature =>
      CryptoHash.castHash
        $ CryptoHashable.hash
        $ Prod.mk slot
        $ Prod.mk party
        $ Prod.mk proof
        $ Prod.mk bodyHash signature

namespace Header

  def msgID (h : Header) : Slot × Party :=
    ⟨ Header.slot h , Header.party h ⟩

  def matche (h : Header) (b : Body) : Prop :=
    Header.bodyHash h = CryptoHashable.hash b

end Header


structure IB where
  header : Header
  body : Body
deriving Repr

instance : CryptoHashable IB where
  hash
  | IB.mk header body => CryptoHash.castHash $ CryptoHashable.hash $ Prod.mk header body


inductive EB where
| mk : Slot → Party → LotteryProof → List (CryptoHash IB) → List (CryptoHash EB) → EB
deriving Repr

instance : CryptoHashable EB where
  hash
  | EB.mk slot party proof ibs ebs =>
      CryptoHash.castHash
        $ CryptoHashable.hash
        $ Prod.mk slot
        $ Prod.mk party
        $ Prod.mk proof
        $ Prod.mk ibs ebs

namespace EB

  def slot (eb : EB) : Slot :=
    match eb with
    | mk s _ _ _ _ => s

  def party (eb : EB) : Party :=
    match eb with
    | mk _ p _ _ _ => p

  def proof (eb : EB) : LotteryProof :=
    match eb with
    | mk _ _ p _ _ => p

  def ibs (eb : EB) : List (CryptoHash IB) :=
    match eb with
    | mk _ _ _ i _ => i

  def ebs (eb : EB) : List (CryptoHash EB) :=
    match eb with
    | mk _ _ _ _ e => e

end EB


structure Vote where
  voter : Party
  ebHash : CryptoHash EB
deriving Repr

instance : CryptoHashable Vote where
  hash
  | Vote.mk voter ebHash => CryptoHash.castHash $ CryptoHashable.hash $ Prod.mk voter ebHash


end Leios.Messages
