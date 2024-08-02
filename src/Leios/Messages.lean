import Leios.Base
import Leios.BLS
import Leios.Crypto
import Leios.Primitives

open Leios.Crypto (CryptoHash CryptoHashable LotteryProof)
open Leios.Base
open Leios.BLS (Signature)
open Leios.Primitives


namespace Leios.Messages


structure mid where
  slot : Slot
  party : Party
deriving Repr, BEq, Hashable


structure Message (Header : Type) (Body : Type) where
  msgID : Header → mid
  matche : Header → Body → Bool


namespace IB

  structure Body where
    txs : List Tx
  deriving Repr, BEq, Hashable

  instance : CryptoHashable Body where
    hash := CryptoHash.castHash ∘ CryptoHashable.hash ∘ Body.txs

  structure Header where
    slot : Slot
    party : Party
    proof : LotteryProof
    bodyHash : CryptoHash Body
    signature : Signature
  deriving Repr, BEq, Hashable

  instance : CryptoHashable Header where
    hash
    | Header.mk slot party proof bodyHash signature =>
        CryptoHash.castHash
          $ CryptoHashable.hash
          $ Prod.mk slot
          $ Prod.mk party
          $ Prod.mk proof
          $ Prod.mk bodyHash signature

  def IBMessage : Message Header Body where
    msgID
    | Header.mk slot party _ _ _ => ⟨ slot , party ⟩
    matche header body :=
      Header.bodyHash header == CryptoHashable.hash body

end IB

structure IB where
  header : IB.Header
  body : IB.Body
deriving Repr, BEq, Hashable

instance : CryptoHashable IB where
  hash
  | IB.mk header body => CryptoHash.castHash $ CryptoHashable.hash $ Prod.mk header body


inductive EB where
| mk : Slot → Party → LotteryProof → List (CryptoHash IB) → List (CryptoHash EB) → EB
deriving Repr, BEq, Hashable

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

def EBMessage : Message EB Unit where
  msgID
  | EB.mk slot party _ _ _ => ⟨ slot , party ⟩
  matche _ _ := true


structure Vote where
  slot : Slot
  voter : Party
  ebHash : CryptoHash EB
deriving Repr, BEq, Hashable

instance : CryptoHashable Vote where
  hash
  | Vote.mk slot voter ebHash =>
    CryptoHash.castHash
      $ CryptoHashable.hash
      $ Prod.mk slot
      $ Prod.mk voter ebHash

def VoteMessage : Message Vote Unit where
  msgID
  | Vote.mk slot party _ => ⟨ slot , party ⟩
  matche _ _ := true


end Leios.Messages
