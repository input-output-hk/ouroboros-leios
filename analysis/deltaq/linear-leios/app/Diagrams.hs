module Main where

import DeltaQ.Diagram (renderOutcomeDiagram)
import DeltaQ.Class (Outcome ((.>>.), (./\.)), ProbabilisticOutcome (choices))
import DeltaQ.Expr (O, var)
import Diagrams.Backend.SVG (renderSVG)
import Diagrams.Prelude (mkWidth)

-- | Outcome expression for fetching transactions, reflecting the TxCache Markov model.
--
-- Transition matrix: M = [[1-p, p], [1-p/2, p/2]]
-- Stationary distribution: π₁ = (2-p)/(2+p), π₂ = 2p/(2+p)
-- Steady-state hit rate: hitRate = π₂·p + π₁·(1-p)
--
-- For p = 0.75: π₁ = 5/11, π₂ = 6/11, hitRate = 23/44
fetchingTxsO :: O
fetchingTxsO = choices [(hitRate, var "cached"), (1 - hitRate, var "fetchTx")]
  where
    p :: Rational
    p = 3 / 4
    π_1 = (2 - p) / (2 + p)
    π_2 = 2 * p / (2 + p)
    hitRate :: Rational
    hitRate = π_2 * p + π_1 * (1 - p)

validateEBDiagram :: O
validateEBDiagram =
    (var "sendRBBody" .>>. var "applyTxs")
    ./\. (var "fetchingEB" .>>. fetchingTxsO)
    .>>. var "reapplyTxs"

main :: IO ()
main =
    renderSVG "docs/EB-diffusion.svg" (mkWidth 700)
    $ renderOutcomeDiagram validateEBDiagram
