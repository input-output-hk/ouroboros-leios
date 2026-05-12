-- | Leios Common
module DeltaQ.Common (
  -- * Backend
  DQ,
  unwrap,

  -- * Combinators
  doAll,
  doSequentially,
) where

import DeltaQ (
  Outcome ((./\.), (.>>.)),
  wait,
 )
import qualified DeltaQ.PiecewisePolynomial as PW
import DeltaQ.Progress (Progress (unProgress))

-- | Backend used throughout the leios-deltaq library. Wrapping the
-- piecewise-polynomial backend in 'Progress' lets binaries that opt in
-- (via 'DeltaQ.Progress.withProgress'/'withStdoutProgress') observe which
-- operations the model triggers; binaries that don't opt in see no events.
type DQ = Progress PW.DQ

-- | Drop the progress wrapper to access the underlying piecewise-polynomial
-- representation (for direct interop with @DeltaQ.PiecewisePolynomial@).
unwrap :: DQ -> PW.DQ
unwrap = unProgress

doAll :: [DQ] -> DQ
doAll = foldr (./\.) (wait 0)

doSequentially :: [DQ] -> DQ
doSequentially = foldr (.>>.) (wait 0)
