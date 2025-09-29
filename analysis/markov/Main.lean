
import Linleios


def env : Environment := makeEnvironment 0.05 1 4 7

def s0 : Probabilities := default
def sn := simulate (@forge env) s0 5
def pn := totalProbability sn

def main : IO Unit :=
  do
    IO.println $ (reprPrec sn 0).pretty
    IO.println $ (reprPrec pn 0).pretty
