import Lean.Data
import Leios.Messages

open Lean (HashMap HashSet)
open Leios.Base
open Leios.Messages


namespace Leios.FFD


structure Parameters where
  deltaHdr : Nat
  d : Nat
  C : Float
deriving Repr, BEq


structure Variables where
  hdrs : HashSet (Header × Slot × Parties)
  bdys : HashSet (Header × IB × Slot × Parties)
  prefHdr : HashMap MsgID Header
deriving Inhabited


class Adversary (s : Type) where
  adversarialHeaders : Parameters → Slot → Party → StateM s (HashSet Header)
  adversarialBodies : Parameters → Slot → Party → StateM s (HashSet IB)


def NullAdversary := Unit
deriving Repr, Inhabited

instance : Adversary NullAdversary where
  adversarialHeaders _ _ _ := pure default
  adversarialBodies _ _ _ := pure default


def hasHdr : Party → MsgId → Variables → Bool :=
  sorry


def hashPoE : Party → MsgId → Variables → Bool :=
  sorry


def hasBdy : Party → MsgId → Variables → Bool :=
  sorry


def HdrsAdd : Header → Slot → Party → Variables → Variables :=
  sorry


def BdysAdd : Header → Body → Slot → Party → Variables → Variables :=
  sorry


def newerBdys : Header → Variables → Nat :=
  sorry


def DiffFB : Parameters → Slot → Header → IB → StateM Variables Unit :=
  sorry


def DiffHdr : Parameters → Slot → Header → StateM Variables Unit :=
  sorry


def FetchHdrs [Adversary a] : Party → StateM (Variables × a) (HashSet Header) :=
  sorry


def FetchBdys [Adversary a] : Party → StateM (Variables × a) (HashSet Header) :=
  sorry


end Leios.FFD
