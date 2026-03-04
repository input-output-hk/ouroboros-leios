-- | Leios Common
module DeltaQ.Common (
  doAll,
  doSequentially,
) where

import DeltaQ (
  DQ,
  Outcome ((./\.), (.>>.)),
  wait,
 )

doAll :: [DQ] -> DQ
doAll = foldr (./\.) (wait 0)

doSequentially :: [DQ] -> DQ
doSequentially = foldr (.>>.) (wait 0)
