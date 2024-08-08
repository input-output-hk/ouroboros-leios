import Lean.Data
import Leios.Messages

open Lean (HashMap HashSet)
open Leios.Base (Parties Slot)
open Leios.Messages (MsgID)


namespace Leios.FFD


structure Parameters where
  deltaHdr : Nat
  d : Nat
  C : Float
deriving Repr, BEq


structure Variables (header : Type) (body : Type) where
  hdrs [BEq header] [Hashable header] : HashSet (header × Slot × Parties)
  bdys [BEq header] [Hashable header] [BEq body] [Hashable body] : HashSet (header × body × Slot × Parties)
  prefHdr : HashMap MsgID header
deriving Inhabited


class Adversary (header : Type) (body : Type) (s : Type) where
  adversarialheaders [Monad m] [MonadStateOf s m] [BEq header] [Hashable header] : Parameters → Slot → Party → m (HashSet header)
  adversarialBodies [Monad m] [MonadStateOf s m] [BEq body] [Hashable body] : Parameters → Slot → Party → m (HashSet body)


def NullAdversary := Unit
deriving Repr, Inhabited

instance : Adversary header body NullAdversary where
  adversarialheaders _ _ _ := pure default
  adversarialBodies _ _ _ := pure default


def hasHdr [MonadReaderOf (Variables header body) m] : Party → MsgID → m Bool :=
  sorry


def hashPoE [MonadReaderOf (Variables header body) m] : Party → MsgID → m Bool :=
  sorry


def hasBdy [MonadReaderOf (Variables header body) m] : Party → MsgID → m Bool :=
  sorry


def HdrsAdd [MonadStateOf (Variables header body) m] : header → Slot → Party → m Unit :=
  sorry


def BdysAdd [MonadStateOf (Variables header body) m] : header → body → Slot → Party → m Unit :=
  sorry


def newerBdys [MonadReaderOf (Variables header body) m] : header → m Nat :=
  sorry


def DiffFB [MonadStateOf (Variables header body) m] : Parameters → Slot → header → IB → m Unit :=
  sorry


def DiffHdr [MonadStateOf (Variables header body) m] : Parameters → Slot → header → m Unit :=
  sorry


def FetchHdrs [BEq header] [Hashable header] [Adversary header body a] [MonadReaderOf (Variables header body × a) m]: Party → m (HashSet header) :=
  sorry


def FetchBdys [BEq body] [Hashable body] [Adversary header body a] [MonadReaderOf (Variables header body × a) m] : Party → m (HashSet body) :=
  sorry


end Leios.FFD
