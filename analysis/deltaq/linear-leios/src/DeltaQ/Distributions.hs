-- | Distributions
module DeltaQ.Distributions (
  measuredDQ,
  expDQ,
  normalDQ,
  logNormalDQ,
  scaleMixtureDQ,
) where

import DeltaQ

import qualified Statistics.Distribution as S
import qualified Statistics.Distribution.Exponential as S
import qualified Statistics.Distribution.Lognormal as S
import qualified Statistics.Distribution.Normal as S

type Measurements = [(Rational, Rational)]

-- | 'measuredDQ'
--
-- https://github.com/DeltaQ-SD/deltaq/issues/75#issuecomment-3334080165
measuredDQ :: Measurements -> DQ
-- we have a (non-empty) list of (probability, delay), ordered on the delays,
-- with probabilities assumed monotonic
measuredDQ delays = choices dataPoints
 where
  -- we add a (0, 0) point at the beginning to ensure that the first delay is always 0
  extendedData = if head delays == (0, 0) then delays else (0, 0) : delays
  -- the weight of each point is the difference in probability
  dataPoints =
    [(p' - p, delayComponent d' d) | ((p, d), (p', d')) <- zip extendedData (tail extendedData)]
  -- if we have two delays the same, we simply wait for that time,
  -- otherwise we use a uniform distribution between the two delays
  delayComponent d1 d2 = if d1 == d2 then wait d1 else uniform d1 d2

-- given a list and a function f, create list of pairs (f x, x)
pairList :: [Rational] -> (Rational -> Rational) -> [(Rational, Rational)]
pairList l f = map (\x -> (f x, x)) l

-- DQ from distribution
distDQ :: S.ContDistr p => p -> DQ
distDQ dist =
  let d = toRational . S.cumulative dist . fromRational
      q = toRational $ S.quantile dist 0.99
   in measuredDQ (pairList [0.0, q / numberSteps .. q] d)
 where
  numberSteps :: Rational
  numberSteps = 10.0

-- | normalDQ
--
-- DQ for log-normal distribution
normalDQ :: Double -> Double -> DQ
normalDQ μ σ = distDQ $ S.normalDistr μ σ

-- | logNormalDQ
--
-- DQ for log-normal distribution
logNormalDQ :: Double -> Double -> DQ
logNormalDQ μ σ = distDQ $ S.lognormalDistr μ σ

-- | expDQ
--
-- DQ for exponential distribution
expDQ :: Double -> DQ
expDQ = distDQ . S.exponential

-- | scaleMixtureDQ
--
-- DQ for scale mixture distribution
scaleMixtureDQ :: Integer -> Double -> Double -> DQ
scaleMixtureDQ n μ σ =
  measuredDQ
    ( pairList [0.0, upper / numberSteps .. upper] $
        toRational . scaleMixtureCDF . fromRational
    )
 where
  numberSteps = 10.0
  upper = toRational $ (fromIntegral n) * μ + 3 * (sqrt (fromIntegral n)) * σ

  scaleMixtureCDF :: Double -> Double
  scaleMixtureCDF x =
    sum
      ( map
          ( \k ->
              S.cumulative (S.normalDistr ((fromInteger k) * μ) ((fromInteger k) * σ)) x
          )
          [1 .. n]
      )
      / fromInteger n
