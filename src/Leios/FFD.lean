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


structure Variables (Header : Type) (Body : Type) where
  hdrs [BEq Header] [Hashable Header] : HashSet (Header × Slot × Parties)
  bdys [BEq Header] [Hashable Header] [BEq Body] [Hashable Body] : HashSet (Header × Body × Slot × Parties)
  prefHdr : HashMap mid Header
deriving Inhabited


class Adversary (Header : Type) (Body : Type) (s : Type) where
  adversarialHeaders [Monad m] [MonadStateOf s m] [BEq Header] [Hashable Header] : Parameters → Slot → Party → m (HashSet Header)
  adversarialBodies [Monad m] [MonadStateOf s m] [BEq Body] [Hashable Body] : Parameters → Slot → Party → m (HashSet Body)


def NullAdversary := Unit
deriving Repr, Inhabited

instance : Adversary Header Body NullAdversary where
  adversarialHeaders _ _ _ := pure default
  adversarialBodies _ _ _ := pure default


def hasHdr [MonadReaderOf (Variables Header Body) m] : Party → mid → m Bool :=
  sorry


def hashPoE [MonadReaderOf (Variables Header Body) m] : Party → mid → m Bool :=
  sorry


def hasBdy [MonadReaderOf (Variables Header Body) m] : Party → mid → m Bool :=
  sorry


def HdrsAdd [MonadStateOf (Variables Header Body) m] : Header → Slot → Party → m Unit :=
  sorry


def BdysAdd [MonadStateOf (Variables Header Body) m] : Header → Body → Slot → Party → m Unit :=
  sorry


def newerBdys [MonadReaderOf (Variables Header Body) m] : Header → m Nat :=
  sorry


def DiffFB [MonadStateOf (Variables Header Body) m] : Parameters → Slot → Header → IB → m Unit :=
  sorry


def DiffHdr [MonadStateOf (Variables Header Body) m] : Parameters → Slot → Header → m Unit :=
  sorry


def FetchHdrs [BEq Header] [Hashable Header] [Adversary Header Body a] [MonadReaderOf (Variables Header Body × a) m]: Party → m (HashSet Header) :=
  sorry


def FetchBdys [BEq Body] [Hashable Body] [Adversary Header Body a] [MonadReaderOf (Variables Header Body × a) m] : Party → m (HashSet Body) :=
  sorry


end Leios.FFD
