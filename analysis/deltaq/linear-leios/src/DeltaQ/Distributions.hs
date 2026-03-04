-- | Distributions
module DeltaQ.Distributions (
  measuredDQ,
  expDQ,
  logNormalDQ,
) where

import DeltaQ

import qualified Statistics.Distribution as S
import qualified Statistics.Distribution.Exponential as S
import qualified Statistics.Distribution.Lognormal as S

type Measurements = [(Double, Double)]

-- | 'measuredDQ'
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
pairList :: [Double] -> (Double -> Double) -> [(Double, Double)]
pairList l f = map (\x -> (f x, x)) l

-- steps for discretization
numberSteps :: Double
numberSteps = 10.0

-- DQ for log-normal distribution
logNormalDQ :: Double -> Double -> DQ
logNormalDQ x y =
  let dist = S.lognormalDistr x y
      d = S.cumulative dist
      q = S.quantile dist 0.99
   in measuredDQ $ pairList [0.0, q / numberSteps .. q] d

-- DQ for exponential distribution
expDQ :: Double -> DQ
expDQ r =
  let dist = S.exponential r
      d = S.cumulative dist
      q = S.quantile dist 0.99
   in measuredDQ $ pairList [0.0, q / numberSteps .. q] d
