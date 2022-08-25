{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module VizChart where

import           Data.Functor
import           Data.Bifunctor

import qualified Graphics.Rendering.Cairo as Cairo

import qualified Graphics.Rendering.Chart.Easy          as Chart
import qualified Graphics.Rendering.Chart.Backend.Cairo as Chart

import Viz


chartVizualisation :: (Int, Int) 
                   -> Chart.EC (Chart.Layout Double Double) ()
                   -> Vizualisation
chartVizualisation size chart =
    Viz VizModel {
          initModel,
          stepModel
        }
        VizRender {
          vizSize  = size,
          renderModel
        }
  where
    initModel :: ()
    initModel = ()

    stepModel :: Float -> () -> ()
    stepModel _delta () = ()

    renderModel () = renderChart (bimap fromIntegral fromIntegral size) chart

renderChart :: (Chart.Default r, Chart.ToRenderable r)
            => (Double, Double) -> Chart.EC r () -> Cairo.Render ()
renderChart (width, height) =
    void
  . Chart.runBackend (Chart.defaultEnv Chart.bitmapAlignmentFns)
  . flip Chart.render (width, height)
  . Chart.toRenderable
  . Chart.execEC

