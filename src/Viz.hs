{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}

module Viz where

import qualified Data.Time as Time
import           Data.IORef
import           Data.Functor.Contravariant

import           Control.Monad.IO.Class
import           Control.Monad.Class.MonadTime (Time(Time), DiffTime, diffTime, addTime)

import qualified Graphics.Rendering.Cairo as Cairo
import qualified Graphics.UI.Gtk as Gtk
import           Graphics.UI.Gtk (AttrOp((:=)))


------------------------------------------------------------------------------
-- Visualisation
--

data Vizualisation where
       Viz :: VizModel  model
           -> VizRender model
           -> Vizualisation

data VizModel model =
     VizModel {
       initModel :: model,
       stepModel :: DiffTime -> Time -> FrameNo -> model -> model
     }

data VizRender model =
     VizRender {
       renderSize    :: (Int, Int),
       renderChanged :: Time -> FrameNo -> model -> Bool,
       renderModel   :: Time -> FrameNo -> model -> Cairo.Render (),
       renderClip    :: Bool
     }
   | VizRenderBeside {
       renderSize    :: (Int, Int),
       renderLeft    :: VizRender model,
       renderRight   :: VizRender model
     }
   | VizRenderAbove {
       renderSize    :: (Int, Int),
       renderAbove   :: VizRender model,
       renderBelow   :: VizRender model
     }

type FrameNo = Int

instance Contravariant VizRender where
    contramap f vizrender@VizRender {renderChanged, renderModel} =
      vizrender {
        renderChanged = \t fn m -> renderChanged t fn (f m),
        renderModel   = \t fn m -> renderModel   t fn (f m)
      }
    contramap f vizrender@VizRenderBeside {renderLeft, renderRight} =
      vizrender {
        renderLeft  = contramap f renderLeft,
        renderRight = contramap f renderRight
      }

    contramap f vizrender@VizRenderAbove {renderAbove, renderBelow} =
      vizrender {
        renderAbove = contramap f renderAbove,
        renderBelow = contramap f renderBelow
      }


data GtkVizConfig =
     GtkVizConfig {
       gtkVizFPS :: Int,

       -- | If @True@, use client side CPU-based Cairo rendering. Otherwise
       -- use Gtk+ offscreen Cairo rendering, which may use GPU acceleration.
       --
       -- For X11-based desktops, the Gtk+ offscreen rendering may actually
       -- use more CPU time as it generates load on the X11 server, which
       -- may or may not itself use GPU acceleration.
       gtkVizCpuRendering :: Bool
     }

defaultGtkVizConfig :: GtkVizConfig
defaultGtkVizConfig =
    GtkVizConfig {
      gtkVizFPS          = 25,
      gtkVizCpuRendering = False
    }

-- | Animate the vizualisation in a Gtk+ window.
--
vizualise :: GtkVizConfig -> Vizualisation -> IO ()
vizualise GtkVizConfig {
            gtkVizFPS,
            gtkVizCpuRendering
          }
          (Viz vizmodel vizrender) = do
    _ <- Gtk.initGUI
    window <- Gtk.windowNew
    canvas <- Gtk.drawingAreaNew

    Gtk.set window
      [ Gtk.containerChild  := canvas
      , Gtk.windowResizable := True
      , Gtk.windowTitle     := ("Visualisation" :: String)
      ]
    let (w,h) = renderSize vizrender in
      Gtk.windowSetDefaultSize window w h

    _ <- Gtk.on window Gtk.keyPressEvent $ Gtk.tryEvent $ do
      name <- Gtk.eventKeyName
      case name of
        "Escape" -> liftIO $ Gtk.widgetDestroy window
        "F11"    -> liftIO $ Gtk.windowFullscreen window
        _        -> return ()

    _ <- Gtk.on window Gtk.objectDestroy $ do
      liftIO Gtk.mainQuit

    surfaceRef <- newIORef Nothing
    modelRef   <- newIORef (stepModelInitial vizmodel)

    _ <- flip Gtk.timeoutAdd (1000 `div` gtkVizFPS) $ do

          (time, frameno, model) <- liftIO $ readIORef modelRef
          let (!time', !frameno', !model') =
                stepModelWithTime vizmodel gtkVizFPS (time, frameno, model)
          writeIORef modelRef (time', frameno', model')
          Gtk.widgetQueueDraw canvas
          return True

    _ <- Gtk.on canvas Gtk.configureEvent $ liftIO $ do
      mdrawwindow <- Gtk.widgetGetWindow canvas
      case mdrawwindow of
        Nothing -> fail "No draw window!"
        Just drawwindow -> do
          w <- Gtk.drawWindowGetWidth  drawwindow
          h <- Gtk.drawWindowGetHeight drawwindow
          surface <- if gtkVizCpuRendering
            then Cairo.createImageSurface Cairo.FormatRGB24 w h
            else Gtk.renderWithDrawWindow drawwindow $
                   Cairo.withTargetSurface $ \mainSurface ->
                      liftIO $ Cairo.createSimilarSurface
                                 mainSurface Cairo.ContentColor w h
          (time, frameno, model) <- readIORef modelRef
          Cairo.renderWith surface $ do
            Cairo.setSourceRGB 1 1 1
            Cairo.rectangle 0 0 (fromIntegral w) (fromIntegral h)
            Cairo.fill
            renderFrame vizrender True time frameno model
          writeIORef surfaceRef (Just surface)
      return True

    _ <- Gtk.on canvas Gtk.draw $ do
      msurface <- liftIO $ readIORef surfaceRef
      case msurface of
        Just surface -> do
          (time, frameno, model) <- liftIO $ readIORef modelRef
          Cairo.renderWith surface $ do
            renderFrame vizrender True time frameno model
          Cairo.setSourceSurface surface 0 0
          Cairo.paint
        Nothing -> return ()

    Gtk.widgetShowAll window
    Gtk.mainGUI

stepModelInitial :: VizModel model
                 -> (Time, FrameNo, model)
stepModelInitial VizModel {initModel, stepModel} =
    (time, frameno, model)
  where
    !frameno  = 0
    !time     = Time 0
    !timestep = 0
    !model    = stepModel timestep time frameno initModel

stepModelWithTime :: VizModel model
                  -> Int
                  -> (Time, FrameNo, model)
                  -> (Time, FrameNo, model)
stepModelWithTime VizModel {stepModel} fps (time, frameno, model) =
    (time', frameno', model')
  where
    !frameno' = frameno + 1

    !time'    | frameno' `mod` fps == 0
              = Time (fromIntegral (frameno' `div` fps) :: DiffTime)
              | otherwise
              = addTime (1 / fromIntegral fps :: DiffTime) time

    !timestep = time' `diffTime` time

    !model'   = stepModel timestep time' frameno' model

renderFrame :: forall model.
               VizRender model -> Bool -> Time -> FrameNo -> model
            -> Cairo.Render ()
renderFrame vizrender forceRender time frame model =
    go 0 0 vizrender
  where
    go :: Int -> Int -> VizRender model -> Cairo.Render ()

    go x y VizRender {
             renderSize = (w,h),
             renderChanged,
             renderModel,
             renderClip
           }
      | forceRender || renderChanged time frame model = do
          Cairo.save
          Cairo.rectangle (fromIntegral x) (fromIntegral y)
                          (fromIntegral w) (fromIntegral h)
          Cairo.setSourceRGB 1 1 1
          if renderClip
            then Cairo.fillPreserve >> Cairo.clip
            else Cairo.fill
          Cairo.translate (fromIntegral x) (fromIntegral y)
          renderModel time frame model
          Cairo.restore

      | otherwise = return ()

    go x y VizRenderAbove {renderAbove, renderBelow} = do
        go x y  renderAbove
        go x y' renderBelow
      where
        y' = y + snd (renderSize renderAbove)

    go x y VizRenderBeside {renderLeft, renderRight} = do
        go x  y renderLeft
        go x' y renderRight
      where
        x' = x + fst (renderSize renderLeft)

-- | Write n seconds of animation frame files (at 25 fps) for the given
-- vizualisation.
--
-- To turn into a video, use a command like:
--
-- > ffmpeg -i example/frame-%d.png -vf format=yuv420p example.mp4
--
writeAnimationFrames :: (Int -> FilePath) -> Int -> Vizualisation -> IO ()
writeAnimationFrames frameFilename runningtime
                     (Viz vizmodel (vizrender :: VizRender model)) =
    let (time, frameno, model) = stepModelInitial vizmodel in
    go time frameno model
  where
    fps :: Num a => a
    fps      = 25
    frameMax = runningtime * fps

    go :: Time -> FrameNo -> model -> IO ()
    go _     !frameno _ | frameno >= frameMax = return ()
    go !time !frameno !model = do
      let (width, height) = renderSize vizrender
      Cairo.withImageSurface Cairo.FormatRGB24 width height $ \surface -> do
        Cairo.renderWith surface $ do
          Cairo.rectangle 0 0 (fromIntegral width) (fromIntegral height)
          Cairo.setSourceRGB 1 1 1
          Cairo.fill
          renderFrame vizrender True time frameno model
        Cairo.surfaceWriteToPNG surface (frameFilename frameno)

      let (time', frameno', model') =
            stepModelWithTime vizmodel fps (time, frameno, model)

      go time' frameno' model'

nullVizModel :: VizModel ()
nullVizModel =
   VizModel {
     initModel = (),
     stepModel = \_ _ _ () -> ()
   }

aboveVizualisation :: Vizualisation -> Vizualisation -> Vizualisation
aboveVizualisation (Viz vizmodela (vizrendera :: VizRender modela))
                    (Viz vizmodelb (vizrenderb :: VizRender modelb)) =
    Viz (pairVizModel vizmodela vizmodelb)
         VizRenderAbove {
           renderSize  = (max wa wb, ha + hb),
           renderAbove = contramap fst vizrendera,
           renderBelow = contramap snd vizrenderb
         }
  where
    (wa,ha) = renderSize vizrendera
    (wb,hb) = renderSize vizrenderb

besideVizualisation :: Vizualisation -> Vizualisation -> Vizualisation
besideVizualisation (Viz vizmodela (vizrendera :: VizRender modela))
                     (Viz vizmodelb (vizrenderb :: VizRender modelb)) =
    Viz (pairVizModel vizmodela vizmodelb)
         VizRenderBeside {
           renderSize  = (wa + wb, max ha hb),
           renderLeft  = contramap fst vizrendera,
           renderRight = contramap snd vizrenderb
         }
  where
    (wa,ha) = renderSize vizrendera
    (wb,hb) = renderSize vizrenderb

pairVizModel :: VizModel modela -> VizModel modelb -> VizModel (modela, modelb)
pairVizModel vizmodela vizmodelb =
    VizModel {
      initModel = (initModel vizmodela,
                   initModel vizmodelb),
      stepModel = \dt t fn (ma, mb) -> (stepModel vizmodela dt t fn ma,
                                        stepModel vizmodelb dt t fn mb)
    }

besideVizRender :: VizRender model
                -> VizRender model
                -> VizRender model
besideVizRender renderLeft renderRight =
     VizRenderBeside {
       renderSize  = (wa + wb, max ha hb),
       renderLeft,
       renderRight
     }
  where
    (wa,ha) = renderSize renderLeft
    (wb,hb) = renderSize renderRight

aboveVizRender :: VizRender model
               -> VizRender model
               -> VizRender model
aboveVizRender renderAbove renderBelow =
     VizRenderAbove {
       renderSize  = (max wa wb, ha + hb),
       renderAbove,
       renderBelow
     }
  where
    (wa,ha) = renderSize renderAbove
    (wb,hb) = renderSize renderBelow


slowmoVizualisation :: DiffTime -> Vizualisation -> Vizualisation
slowmoVizualisation dilation
                   (Viz vizmodel (vizrender :: VizRender model)) =
    Viz vizmodel {
          initModel = (Time 0, initModel vizmodel),
          stepModel = stepModel'
        }
        (adjustVizRenderTime vizrender)
  where
    stepModel' :: DiffTime -> Time -> FrameNo
               -> (Time, model) -> (Time, model)
    stepModel' delta (Time now) frameno (_now, m) =
        (now', stepModel vizmodel delta' now' frameno m)
      where
        delta' :: DiffTime
        delta' = delta * dilation

        now' :: Time
        now' = Time (now * dilation)

    adjustVizRenderTime vr@VizRender {renderChanged, renderModel} =
      vr {
        renderChanged = \_t fn (t, m) -> renderChanged t fn m,
        renderModel   = \_t fn (t, m) -> renderModel   t fn m
      }
    adjustVizRenderTime vr@VizRenderBeside {renderLeft, renderRight} =
      vr {
        renderLeft  = adjustVizRenderTime renderLeft,
        renderRight = adjustVizRenderTime renderRight
      }

    adjustVizRenderTime vr@VizRenderAbove {renderAbove, renderBelow} =
      vr {
        renderAbove = adjustVizRenderTime renderAbove,
        renderBelow = adjustVizRenderTime renderBelow
      }

labelTimeVizRender :: VizRender model
labelTimeVizRender =
    VizRender {
      renderSize    = (400, 20),
      renderChanged = \_t _fn _m -> True,
      renderClip    = False,
      renderModel
    }
  where
    renderModel :: Time -> FrameNo -> model -> Cairo.Render ()
    renderModel (Time t) _fn _m = do
      Cairo.moveTo 5 20
      Cairo.setFontSize 20
      Cairo.setSourceRGB 0 0 0
      Cairo.showText $
        Time.formatTime Time.defaultTimeLocale "Time (sec): %-2ES" t

labelVizRender :: String -> VizRender model
labelVizRender label =
    VizRender {
      renderSize    = (1000, 30),
      renderChanged = \_t _fn _m -> False,
      renderClip    = False,
      renderModel   = \_t _fn _m -> do
        Cairo.selectFontFace ("Sans" :: String)
                             Cairo.FontSlantNormal
                             Cairo.FontWeightBold
        Cairo.setFontSize 25
        Cairo.TextExtents {
          Cairo.textExtentsWidth  = w,
          Cairo.textExtentsHeight = h 
        } <- Cairo.textExtents label
        Cairo.moveTo (max 0 ((1000 - w) / 2)) h
        Cairo.setSourceRGB 0 0 0
        Cairo.showText label
    }

{-
scaleVizualisation :: Double -> Vizualisation -> Vizualisation
scaleVizualisation s (Viz vizmodel (vizrender :: VizRender model rstate)) =
    Viz vizmodel vizrender {
      vizSize     = (round (s * fromIntegral w),
                     round (s * fromIntegral h)),
      renderModel = renderModelScaled
    }
  where
    (w,h) = vizSize vizrender
    renderModelScaled :: model -> rstate -> Cairo.Render rstate
    renderModelScaled m rst = do
      Cairo.save
      Cairo.scale s s
      rst' <- renderModel vizrender m rst
      Cairo.restore
      return rst'

viewportVizualisation :: Int -> Int -> Vizualisation -> Vizualisation
viewportVizualisation width height (Viz vizmodel vizrender) =
    Viz vizmodel vizrender { vizSize = (width, height) }

occasionalVizualisation :: forall model rstate.
                           (Int, Int)
                        -> rstate
                        -> (model -> rstate -> (rstate, Maybe (Cairo.Render ())))
                        -> VizRender model (rstate, Maybe Cairo.Surface)
occasionalVizualisation vizSize@(w,h) initRender' renderModel' =
    VizRender {
      vizSize,
      initRender = (initRender', Nothing),
      renderModel
    }
  where
    renderModel :: model
                -> (rstate, Maybe Cairo.Surface)
                -> Cairo.Render (rstate, Maybe Cairo.Surface)
    renderModel model (rst, msurface) =
      case renderModel' model rst of
        (rst', Just render) -> do
          surface <- Cairo.withTargetSurface $ \mainSurface ->
            liftIO $ Cairo.createSimilarSurface
                       mainSurface Cairo.ContentColor w h
          Cairo.renderWith surface $ do
            Cairo.setSourceRGB 1 1 1
            Cairo.rectangle 0 0 (fromIntegral w) (fromIntegral h)
            Cairo.fill
            Cairo.setSourceRGB 0 0 0
            render
          Cairo.setSourceSurface surface 0 0
          Cairo.paint
          return (rst', Just surface)

        (rst', Nothing)
          | Just surface <- msurface -> do
              Cairo.setSourceSurface surface 0 0
              Cairo.paint
              return (rst', msurface)

          | otherwise -> return (rst', msurface)
-}
