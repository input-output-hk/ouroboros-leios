
import Linleios


def env : Environment := makeEnvironment 0.05 0.95 0.90 1 4 7

def s0 : Probabilities := default
def sn := simulate env s0 10
def pn := totalProbability sn

def main : IO Unit :=
  do
    let print {α : Type} [Repr α] (x : α) : IO Unit := IO.println (reprPrec x 0).pretty
    print $ prune 0 sn
    print pn
