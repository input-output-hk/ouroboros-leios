
import Linleios


def env : Environment := makeEnvironment 0.05 0.95 0.90 600 0.75 1 4 7

def sn := simulate env default 1e-6 25

def main : IO Unit :=
  do
    let print {α : Type} [Repr α] (x : α) : IO Unit := IO.println (reprPrec x 0).pretty
    IO.println ""
    print sn
    IO.println ""
    print $ ebDistribution sn
    IO.println ""
    print $ ebEfficiency sn
    IO.println ""
    print $ 1 - totalProbability sn
