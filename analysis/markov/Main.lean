
import Linleios


def env : Environment := makeEnvironment 0.05 0.95 0.90 600 0.75 1 4 7

def s0 : Probabilities := default
def sn := simulate env s0 1e-6 2
def pn := totalProbability sn

def main : IO Unit :=
  do
    let print {α : Type} [Repr α] (x : α) : IO Unit := IO.println (reprPrec x 0).pretty
    print sn
    print $ 1 - pn
