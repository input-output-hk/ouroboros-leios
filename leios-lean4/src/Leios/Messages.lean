import Leios.Base
import Leios.BLS
import Leios.Crypto
import Leios.Primitives
import Leios.Vote
import Leios.VRF

open Leios.Crypto (CryptoHash CryptoHashable)
open Leios.Base (Party Slot Tx)
open Leios.BLS (Signature)
open Leios.Vote (ElectionID Vote)
open Leios.VRF (Proof)


namespace Leios.Messages


structure MsgID where
  slot : Slot
  party : Party
deriving Repr, BEq, Hashable


structure Message (header : Type) (body : Type) where
  msgID : header → MsgID
  matche : header → body → Bool


namespace IB

  structure Body where
    txs : List Tx
  deriving Repr, BEq, Hashable

  instance : CryptoHashable Body where
    hash := CryptoHash.castHash ∘ CryptoHashable.hash ∘ Body.txs

  structure Header where
    slot : Slot
    party : Party
    proof : Proof
    bodyHash : CryptoHash Body
    signature : Signature (Slot × Party × Proof × CryptoHash Body)
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
| mk : Slot → Party → Proof → List (CryptoHash IB) → List (CryptoHash EB) → EB
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

  def proof (eb : EB) : Proof :=
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


structure VoteEB where
  eid : ElectionID
  ebHash : CryptoHash EB
  vote : Vote (CryptoHash EB)
deriving Repr, BEq, Hashable

instance : CryptoHashable VoteEB where
  hash
  | VoteEB.mk eid ebHash vote =>
    CryptoHash.castHash
      $ CryptoHashable.hash
      $ Prod.mk eid
      $ Prod.mk ebHash vote

def VoteMessage : Message VoteEB Unit where
  msgID
  | VoteEB.mk eid _ _ => ⟨ eid.slot , eid.party ⟩
  matche _ _ := true


end Leios.Messages
