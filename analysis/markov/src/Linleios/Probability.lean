
import Linleios.Util


/--
Number of stake pools.
-/
def nPools : Nat := 2500

/--
Sortition results.
-/
structure Sortition where
  stake : Float
  probability : Float
deriving Repr

/--
Fait Accompli sortition.
-/
def faSortition (nPools n : Nat) : List Sortition :=
  let S (i : Nat) := ((nPools - i + 1).toFloat / nPools.toFloat)^10 - ((nPools - i).toFloat / nPools.toFloat)^10
  let ρ (i : Nat) := 1 - ((nPools - i).toFloat / nPools.toFloat)^10
  let test (n i : Nat) : Bool := (1 - S i / ρ i)^2 < (n - i).toFloat / (n - i + 1).toFloat
  let i := (List.range nPools).map $ Add.add 1
  let ⟨ persistent , nonpersistent ⟩ := i.partition $ test n
  let ρStar := ρ $ persistent.length + 1
  let persistent' := persistent.map $ fun i ↦ {stake := S i, probability := 1}
  let nonpersistent' :=
    nonpersistent.map $ fun i ↦
      let Si := S i
      {stake := Si, probability := Si / ρStar}
  persistent' ++ nonpersistent'

/--
Compute the mean and standard deviation of the committee size, given the probability of a successful vote and a target committee size.
-/
def voteDistribution (pSuccessfulVote : Float) (committeeSize : Nat) : Float × Float :=
  let sortition := faSortition nPools committeeSize
  let μ := (sortition.map $ fun s ↦ let p := s.probability * pSuccessfulVote; s.stake * p).sum
  let σ := (sortition.map $ fun s ↦ let p := s.probability * pSuccessfulVote; (s.stake * s.stake * p * (1 - p))).sum.sqrt
  ⟨ μ , σ ⟩

/--
Compute the probability of a quorum, given the probability of a successful vote, the target committee size, and the quorum fraction.
-/
def pQuorum (pSuccessfulVote committeeSize τ : Float) : Float :=
  let ⟨ μ , σ ⟩ := voteDistribution pSuccessfulVote committeeSize.toUInt64.toNat
  1 - cdfGaussian τ μ σ

/--
Compute a realistic stake distribution for the specified number of pools.
-/
def stakeDistribution (nPools : Nat) : List Float :=
  (faSortition nPools 700).map Sortition.stake
