{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module VizSim where

import Data.Foldable as Foldable

import Control.Monad.Class.MonadTime.SI (DiffTime, Time)

import Viz

-- | A vizualisation model specialised to trace-based simulations: accumulate
-- a vizualisation state from trace events in a foldl style.
data SimVizModel event vizstate
  = SimVizModel
      [(Time, event)]
      !vizstate

simVizModel ::
  forall event vizstate.
  -- | Accumulate an event
  (Time -> event -> vizstate -> vizstate) ->
  -- | Prune the state at a time
  (Time -> vizstate -> vizstate) ->
  -- | Initial viz state
  vizstate ->
  [(Time, event)] ->
  VizModel (SimVizModel event vizstate)
simVizModel accumEventVizState pruneVisState initVizState trace =
  VizModel
    { initModel
    , stepModel
    }
 where
  initModel :: SimVizModel event vizstate
  initModel = SimVizModel trace initVizState

  stepModel ::
    DiffTime ->
    Time ->
    FrameNo ->
    SimVizModel event vizstate ->
    SimVizModel event vizstate
  stepModel _delta now _frameno (SimVizModel events vstate) =
    SimVizModel events' vstate'
   where
    (deltaEvents, events') = span (\(ts, _) -> ts <= now) events
    vstate' =
      pruneVisState now $
        foldl'
          (\s (t, e) -> accumEventVizState t e s)
          vstate
          deltaEvents
