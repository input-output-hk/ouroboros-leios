{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module VizSim where

import           Data.Foldable as Foldable

import           Control.Monad.Class.MonadTime (Time(Time), addTime)

import Viz


-- | A vizualisation model specialised to trace-based simulations: accumulate
-- a vizualisation state from trace events in a foldl style.
--
data SimVizModel event vizstate =
       SimVizModel
         !Time
          [(Time, event)]
         !vizstate

simVizModel :: forall event vizstate.
               (Time -> event -> vizstate -> vizstate) -- ^ Accumulate an event
            -> (Time ->          vizstate -> vizstate) -- ^ Prune the state at a time
            -> vizstate                        -- ^ Initial viz state
            -> [(Time, event)]
            -> VizModel (SimVizModel event vizstate)
simVizModel accumEventVizState pruneVisState initVizState trace =
    VizModel {
      initModel,
      stepModel
    }
  where
    initModel :: SimVizModel event vizstate
    initModel = SimVizModel (Time 0) trace initVizState

    stepModel :: Float -> SimVizModel event vizstate -> SimVizModel event vizstate
    stepModel delta (SimVizModel now events vstate) =
        SimVizModel now' events' vstate'
      where
        now'                   = realToFrac delta `addTime` now
        (deltaEvents, events') = span (\(ts, _) -> ts <= now') events
        vstate'                = pruneVisState now'
                               $ foldl' (\s (t, e) -> accumEventVizState t e s)
                                        vstate
                                        deltaEvents

