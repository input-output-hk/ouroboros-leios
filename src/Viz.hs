{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}

module Viz where

import qualified Data.Time as Time
import           Data.IORef

import           Control.Monad.IO.Class
import           Control.Monad.Class.MonadTime (DiffTime)

import qualified Graphics.Rendering.Cairo as Cairo
import qualified Graphics.UI.Gtk as Gtk
import           Graphics.UI.Gtk (AttrOp((:=)))


------------------------------------------------------------------------------
-- Visualisation
--

data Vizualisation = forall model. Viz (VizModel model) (VizRender model)

data VizModel model =
     VizModel {
       initModel :: model,
       stepModel :: Float -> model -> model
     }

data VizRender model =
     VizRender {
         vizSize     :: (Int, Int),
         renderModel :: model -> Cairo.Render ()
     }


-- | Animate the vizualisation in a Gtk+ window.
--
vizualise :: Vizualisation -> IO ()
vizualise (Viz VizModel  {initModel, stepModel}
               VizRender {vizSize, renderModel}) = do
    _ <- Gtk.initGUI
    window <- Gtk.windowNew
    canvas <- Gtk.drawingAreaNew

    Gtk.set window
      [ Gtk.containerChild  := canvas
      , Gtk.windowResizable := True
      , Gtk.windowTitle     := ("Visualisation" :: String)
      ]
    Gtk.windowSetDefaultSize window (fst vizSize) (snd vizSize)

    _ <- Gtk.on window Gtk.keyPressEvent $ Gtk.tryEvent $ do
      "Escape" <- Gtk.eventKeyName
      liftIO $ Gtk.widgetDestroy window

    _ <- Gtk.on window Gtk.objectDestroy $ do
      liftIO Gtk.mainQuit

    let fps :: Num a => a
        fps = 25
    modelRef <- newIORef (stepModel 0 initModel)

    _ <- Gtk.timeoutAdd
           (do modifyIORef' modelRef (stepModel (1/fps))
               Gtk.widgetQueueDraw canvas
               return True)
           (1000 `div` fps)

    _ <- Gtk.on canvas Gtk.draw $ do
      model <- liftIO $ readIORef modelRef
      renderModel model

    Gtk.widgetShowAll window
    Gtk.mainGUI

-- | Write n seconds of animation frame files (at 25 fps) for the given
-- vizualisation.
--
-- To turn into a video, use a command like:
--
-- > ffmpeg -i example/frame-%d.png -vf format=yuv420p example.mp4
--
writeAnimationFrames :: (Int -> FilePath) -> Int -> Vizualisation -> IO ()
writeAnimationFrames frameFilename runningtime
                     (Viz VizModel  {initModel, stepModel}
                          VizRender {vizSize = (width, height), renderModel}) =
    go 0 (stepModel 0 initModel)
  where
    fps :: Num a => a
    fps      = 25
    frameMax = runningtime * fps
    go !frameno _ | frameno >= frameMax = return ()
    go !frameno !model = do
      Cairo.withImageSurface Cairo.FormatRGB24 width height $ \surface -> do
        Cairo.renderWith surface $ do
          Cairo.rectangle 0 0 (fromIntegral width) (fromIntegral height)
          Cairo.setSourceRGB 1 1 1
          Cairo.fill
          renderModel model
        Cairo.surfaceWriteToPNG surface (frameFilename frameno)
      let !model' = stepModel (1/fps) model
      go (frameno + 1) model'

-- | 
aboveVizualisations :: Vizualisation -> Vizualisation -> Vizualisation
aboveVizualisations (Viz vizmodela (vizrendera :: VizRender modela))
                    (Viz vizmodelb (vizrenderb :: VizRender modelb)) =
    Viz VizModel {
          initModel = (initModel vizmodela,
                       initModel vizmodelb),
          stepModel = \dt (ma, mb) -> (stepModel vizmodela dt ma,
                                       stepModel vizmodelb dt mb)
        }
        VizRender {
          vizSize     = (max wa wb, ha + hb),
          renderModel = renderModelPair
        }
  where
    (wa,ha) = vizSize vizrendera
    (wb,hb) = vizSize vizrenderb

    renderModelPair :: (modela, modelb) -> Cairo.Render ()
    renderModelPair (ma, mb) = do
      Cairo.save
      renderModel vizrendera ma
      Cairo.restore

      Cairo.save
      Cairo.translate 0 (fromIntegral ha)
      renderModel vizrenderb mb
      Cairo.restore

besideVizualisations :: Vizualisation -> Vizualisation -> Vizualisation
besideVizualisations (Viz vizmodela (vizrendera :: VizRender modela))
                     (Viz vizmodelb (vizrenderb :: VizRender modelb)) =
    Viz VizModel {
          initModel = (initModel vizmodela,
                       initModel vizmodelb),
          stepModel = \dt (ma, mb) -> (stepModel vizmodela dt ma,
                                       stepModel vizmodelb dt mb)
        }
        VizRender {
          vizSize     = (wa + wb, max ha hb),
          renderModel = renderModelPair
        }
  where
    (wa,ha) = vizSize vizrendera
    (wb,hb) = vizSize vizrenderb

    renderModelPair :: (modela, modelb) -> Cairo.Render ()
    renderModelPair (ma, mb) = do
      Cairo.save
      renderModel vizrendera ma
      Cairo.restore

      Cairo.save
      Cairo.translate (fromIntegral wa) 0
      renderModel vizrenderb mb
      Cairo.restore

timedVizualisation :: Float -> Vizualisation -> Vizualisation
timedVizualisation dilation (Viz vizmodel (vizrender :: VizRender model)) =
    Viz vizmodel {
          initModel = (0, initModel vizmodel),
          stepModel = stepModelWithTime
        }
        vizrender {
          vizSize   = vizSize vizrender,
          renderModel = renderModelWithTime
        }
  where
    stepModelWithTime :: Float -> (DiffTime, model) -> (DiffTime, model)
    stepModelWithTime delta (now, m) =
        (now', stepModel vizmodel delta' m)
      where
        delta' :: Float
        delta' = delta * dilation

        now' :: DiffTime
        now'   = realToFrac delta' + now

    renderModelWithTime :: (DiffTime, model) -> Cairo.Render ()
    renderModelWithTime (now, m) = do
      Cairo.save
      renderModel vizrender m
      Cairo.restore
      Cairo.moveTo 5 20
      Cairo.setFontSize 20
      Cairo.setSourceRGB 0 0 0
      Cairo.showText $
        Time.formatTime Time.defaultTimeLocale "Time (sec): %-2ES" now

scaleVizualisation :: Double -> Vizualisation -> Vizualisation
scaleVizualisation s (Viz vizmodel (vizrender :: VizRender model)) =
    Viz vizmodel vizrender {
      vizSize     = (round (s * fromIntegral w),
                     round (s * fromIntegral h)),
      renderModel = renderModelScaled
    }
  where
    (w,h) = vizSize vizrender
    renderModelScaled :: model -> Cairo.Render ()
    renderModelScaled m = do
      Cairo.save
      Cairo.scale s s
      renderModel vizrender m
      Cairo.restore

viewportVizualisation :: Int -> Int -> Vizualisation -> Vizualisation
viewportVizualisation width height (Viz vizmodel vizrender) =
    Viz vizmodel vizrender { vizSize = (width, height) }
