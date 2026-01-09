-- | Empirical distributions
module DeltaQ.Leios.EmpiricalDistributions (
  measuredDQ,
  empiricalDQ,
) where

import Data.List (sort)
import Data.Ratio ((%))
import DeltaQ

type Measurements = [(Rational, Rational)]

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

-- | 'empiricalDQ'
empiricalDQ :: [Double] -> DQ
empiricalDQ ms =
  measuredDQ $
    zip
      (map toRational [0, (1 % length ms) .. 1])
      (map toRational $ sort ms)
