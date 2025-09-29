
import Linleios


def env : Environment := makeEnvironment 0.05 1 4 7

def s0 : Probabilities := default
def sn := simulate (@forge env) s0 50
def pn := totalProbability sn

def main : IO Unit :=
  do
    let print {α : Type} [Repr α]  (x : α) : IO Unit := IO.println $ (reprPrec x 0).pretty
    print sn
    print pn
