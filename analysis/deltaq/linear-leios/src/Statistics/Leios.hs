-- | The module offers statistics about Ouroboros Leios. The code is taken from
--
-- * Peras
-- * Markov simulation of Leios
module Statistics.Leios (
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

calibrateCommittee :: Double -> Double -> Double
calibrateCommittee n m =
  let f x = sum (map (\s -> 1 - exp (-x * s)) (stakeDistribution n)) - m
   in bisectionSearch f m n 0.5 10

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
