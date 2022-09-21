{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module VizChart where

import           Data.Functor
import           Data.List
import           Data.Ord

import           Control.Monad.Class.MonadTime (Time, DiffTime)

import qualified Graphics.Rendering.Cairo as Cairo

import qualified Graphics.Rendering.Chart.Easy          as Chart
import qualified Graphics.Rendering.Chart.Backend.Cairo as Chart

import ModelTCP
import Viz


chartVizRender :: forall model x y.
                  (Chart.PlotValue x, Chart.PlotValue y)
               => FrameNo
               -> (Time -> FrameNo -> model -> Chart.EC (Chart.Layout x y) ())
               -> VizRender model
chartVizRender skipFrames chart =
    VizRender {
      renderReqSize = (500, 500),
      renderChanged = \_t frameno _model -> frameno `mod` skipFrames == 0,
      renderModel
    }
  where
    renderModel :: Time -> FrameNo -> model -> (Double,Double) -> Cairo.Render ()
    renderModel t nf model size = renderChart size (chart t nf model)

renderChart :: (Chart.Default r, Chart.ToRenderable r)
            => (Double, Double) -> Chart.EC r () -> Cairo.Render ()
renderChart (width, height) =
    void
  . Chart.runBackend (Chart.defaultEnv Chart.bitmapAlignmentFns)
  . flip Chart.render (width, height)
  . Chart.toRenderable
  . Chart.execEC


instance Chart.PlotValue Bytes where
  toValue (Bytes b) = Chart.toValue b
  fromValue v = Bytes (Chart.fromValue v)

  autoAxis = Chart.autoScaledIntAxis $
               Chart.LinearAxisParams
                 (map (\(Bytes n) -> show (n `div` 1024) ++ " kb"))
                 10
                 50

instance Chart.PlotValue DiffTime where
  toValue   t = realToFrac t
  fromValue v = realToFrac v
  autoAxis = autoScaledAxis $
               Chart.LinearAxisParams
                 (map (\t -> show t))
                 10
                 50

autoScaledAxis :: RealFrac a => Chart.LinearAxisParams a -> Chart.AxisFn a
autoScaledAxis lap ps = scaledAxis lap rs ps
  where
    rs = (minimum ps,maximum ps)

scaledAxis :: RealFrac a => Chart.LinearAxisParams a -> (a,a) -> Chart.AxisFn a
scaledAxis lap rs@(minV,maxV) ps =
    Chart.makeAxis' realToFrac realToFrac
      (Chart._la_labelf lap) (labelvs,tickvs,gridvs)
  where
    range []  = (0,1)
    range _   | minV == maxV = if minV==0 then (-1,1) else
                               let d = abs (minV * 0.01) in (minV-d,maxV+d)
              | otherwise    = rs
    labelvs   = map fromRational $ steps (fromIntegral (Chart._la_nLabels lap)) r
    tickvs    = map fromRational $ steps (fromIntegral (Chart._la_nTicks lap))
                                         (minimum labelvs,maximum labelvs)
    gridvs    = labelvs
    r         = range ps

steps :: RealFrac a => a -> (a,a) -> [Rational]
steps nSteps rs@(minV,maxV) = map ((s*) . fromIntegral) [min' .. max']
  where
    s    = chooseStep nSteps rs
    min' :: Integer
    min' = floor   $ realToFrac minV / s
    max' = ceiling $ realToFrac maxV / s


chooseStep :: RealFrac a => a -> (a,a) -> Rational
chooseStep nsteps (x1,x2) = minimumBy (comparing proximity) stepVals
  where
    delta = x2 - x1
    mult  | delta == 0 = 1  -- Otherwise the case below will use all of memory
          | otherwise  = 10 ^^ ((floor $ log10 $ realToFrac $ delta / nsteps)::Integer)
    stepVals = map (mult*) [0.1,0.2,0.25,0.5,1.0,2.0,2.5,5.0,10,20,25,50]
    proximity x = abs $ delta / realToFrac x - nsteps

log10 :: Double -> Double
log10 = logBase 10

