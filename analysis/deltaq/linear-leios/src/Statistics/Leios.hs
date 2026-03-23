-- | The module offers statistics about Ouroboros Leios. The code is taken from
--
-- * Peras
-- * Markov simulation of Leios
module Statistics.Leios (
  calibrateCommittee,
  committeeDistribution,
  quorumProbability,
)
where

import qualified Statistics.Distribution as S
import qualified Statistics.Distribution.Normal as S
import Statistics.Praos (stakeDistribution)

bisectionSearch :: (Double -> Double) -> Double -> Double -> Double -> Integer -> Double
bisectionSearch _ low high _ 0 = (low + high) / 2
bisectionSearch f low high eps maxIter =
  let mid = (low + high) / 2
   in if high - low < eps || abs (f mid) < eps
        then mid
        else
          if f low * f mid < 0
            then bisectionSearch f low mid eps (maxIter - 1)
            else bisectionSearch f mid high eps (maxIter - 1)

-- | Calibrate the Poisson sortition parameter so that the expected committee
-- size equals the target @m@.
--
-- Each SPO @i@ with relative stake @s_i@ is elected to the committee
-- independently with probability @1 - exp(-λ · s_i)@.  The parameter @λ@ is
-- not set directly; instead we solve the implicit equation
--
-- @
-- E[committee size] = Σ_i (1 - exp(-λ · s_i)) = m
-- @
--
-- i.e. we find the root of @f(λ) = Σ_i (1 - exp(-λ · s_i)) - m@ by bisection
-- on the interval @[m, n]@
calibrateCommittee :: Double -> Double -> Double
calibrateCommittee n m =
  let f x = sum (map (\s -> 1 - exp (-x * s)) (stakeDistribution n)) - m
   in bisectionSearch f m n 0.5 10

-- | Compute the mean and standard deviation of the number of successful votes.
--
-- Given the calibrated sortition parameter @λ = calibrateCommittee n m@, the
-- per-SPO probability of being elected /and/ casting a successful vote is
--
-- @p_i = pSuccessfulVote · (1 - exp(-λ · s_i))@
--
-- The total vote count @V = Σ_i X_i@, @X_i ~ Bernoulli(p_i)@, has
--
-- @μ = Σ p_i@,  @σ² = Σ p_i (1 - p_i)@
--
-- and is approximated by a normal distribution to evaluate the quorum
-- probability @P(V ≥ τ · m)@.
committeeDistribution :: Double -> Double -> Double -> (Double, Double)
committeeDistribution n pSuccessfulVote m =
  let m' = calibrateCommittee n m
      ps = map (\s -> pSuccessfulVote * (1 - exp (-m' * s))) (stakeDistribution n)
      μ = sum ps
      σ = sqrt $ sum $ map (\p -> p * (1 - p)) ps
   in (μ, σ)

quorumProbability :: Double -> Double -> Double -> Double -> Double
quorumProbability n pSuccessfulVote m τ =
  let (μ, σ) = (committeeDistribution n pSuccessfulVote) m
   in S.complCumulative (S.normalDistr μ σ) (τ * m)
