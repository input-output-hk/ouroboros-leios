
import Linleios


def env : Environment := makeEnvironment 0.05 1 4 7

def s0 : Probabilities := default
def s1 := evolve (@forge env) s0

def main : IO Unit :=
  IO.println $ (reprPrec s1 0).pretty
