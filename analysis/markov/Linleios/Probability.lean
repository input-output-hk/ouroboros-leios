
import Linleios.Util


def nPools : Nat := 2500

def stakeDistribution (nPools : Nat) : List Float :=
  (List.range nPools).map (fun k => ((k + 1).toFloat / nPools.toFloat)^10 - (k.toFloat / nPools.toFloat)^10)

private def calibrateCommittee(committeeSize : Float) : Float :=
  let stakes : List Float := stakeDistribution nPools
  let f (m : Float) : Float :=
    let ps : List Float := stakes.map (fun s => 1 - Float.exp (- m * s))
    ps.sum - committeeSize
  bisectionSearch f committeeSize nPools.toFloat 0.5 10

private def committeeDistribution (pSuccessfulVote committeeSize : Float) : Float × Float :=
  let stakes : List Float := stakeDistribution nPools
  let m := calibrateCommittee committeeSize
  let ps : List Float := stakes.map (fun s => pSuccessfulVote * (1 - Float.exp (- m * s)))
  let μ := ps.sum
  let σ := (ps.map (fun p => p * (1 - p))).sum.sqrt
  ⟨ μ , σ ⟩

def pQuorum (pSuccessfulVote committeeSize τ : Float) : Float :=
  let ⟨ μ , σ ⟩ := committeeDistribution pSuccessfulVote committeeSize
  1 - cdfGaussian (τ * committeeSize) μ σ
