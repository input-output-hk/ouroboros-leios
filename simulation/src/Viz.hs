{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Viz where

import Control.Monad (when)
import Control.Monad.Class.MonadTime.SI (DiffTime, Time (Time), addTime, diffTime)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Functor.Contravariant (Contravariant (contramap))
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (foldl1', mapAccumL, zip4)
import Data.Ratio ((%))
import qualified Data.Time as Time
import Data.Tree as Tree (Tree (..))
import qualified Graphics.Rendering.Cairo as Cairo
import qualified Graphics.Rendering.Pango.Cairo as Pango
import qualified Graphics.Rendering.Pango.Font as Pango
import qualified Graphics.Rendering.Pango.Layout as Pango
import Graphics.UI.Gtk (AttrOp ((:=)))
import qualified Graphics.UI.Gtk as Gtk

------------------------------------------------------------------------------
-- Visualisation
--

data Vizualisation where
  Viz ::
    VizModel model ->
    Layout (VizRender model) ->
    Vizualisation

data VizModel model = VizModel
  { initModel :: model
  , stepModel :: DiffTime -> Time -> FrameNo -> model -> model
  }

data VizRender model = VizRender
  { renderReqSize :: (Int, Int)
  , renderChanged :: Time -> FrameNo -> model -> Bool
  , renderModel ::
      Time ->
      FrameNo ->
      model ->
      (Double, Double) ->
      Cairo.Render ()
  }

data Layout a
  = Layout a
  | LayoutReqSize !Int !Int (Layout a)
  | LayoutExpand (Layout a)
  | LayoutFixed (Layout a)
  | -- | Preserve the aspect ratio
    LayoutAspect (Layout a)
  | LayoutScaleBy !Double (Layout a)
  | LayoutScaleFit (Layout a)
  | LayoutBeside [Layout a]
  | LayoutAbove [Layout a]
  | LayoutOver [Layout a]
  deriving (Functor)

type FrameNo = Int

instance Contravariant VizRender where
  contramap f vizrender@VizRender{renderChanged, renderModel} =
    vizrender
      { renderChanged = \t fn m -> renderChanged t fn (f m)
      , renderModel = \t fn m -> renderModel t fn (f m)
      }

stepModelInitial ::
  VizModel model ->
  (Time, FrameNo, model)
stepModelInitial VizModel{initModel, stepModel} =
  (time, frameno, model)
 where
  !frameno = 0
  !time = Time 0
  !timestep = 0
  !model = stepModel timestep time frameno initModel

stepModelWithTime ::
  VizModel model ->
  Int ->
  (Time, FrameNo, model) ->
  (Time, FrameNo, model)
stepModelWithTime VizModel{stepModel} fps (time, frameno, model) =
  (time', frameno', model')
 where
  !frameno' = frameno + 1

  !time'
    | frameno' `mod` fps == 0 =
        Time (fromIntegral (frameno' `div` fps) :: DiffTime)
    | otherwise =
        addTime (1 / fromIntegral fps :: DiffTime) time

  !timestep = time' `diffTime` time

  !model' = stepModel timestep time' frameno' model

data LayoutTile a = LayoutTile !Tile a

data Tile = Tile
  { tileX :: !Int
  , tileY :: !Int
  , tileW :: !Int
  , tileH :: !Int
  , tileScale :: !Double
  -- ^ Scale the content
  , tileClear :: !Bool
  -- ^ Should the tile be cleared before drawing
  }

-- | Perform layout for a given size (w,h), yielding a set of tiles.
layoutTiles ::
  forall a.
  (Int, Int) ->
  Layout a ->
  Tree LayoutProperties ->
  [LayoutTile a]
layoutTiles allocToplevel =
  allocate (0, 0) allocToplevel 1.0 True
 where
  allocate ::
    (Int, Int) ->
    (Int, Int) ->
    Double ->
    Bool ->
    Layout a ->
    Tree LayoutProperties ->
    [LayoutTile a]
  allocate (x, y) (w, h) scale clear layout (Tree.Node props lps) =
    case (layout, lps) of
      (Layout a, []) ->
        [LayoutTile (Tile x y w h scale clear) a]
      (LayoutReqSize _rw _rh l, [lp]) ->
        -- changes the requested size, not the allocated size
        allocate (x, y) (w, h) scale clear l lp
      (LayoutExpand l, [lp]) ->
        allocate (x, y) (w, h) scale clear l lp
      (LayoutFixed l, [lp]) ->
        allocate (x, y) (w, h) scale clear l lp
      (LayoutAspect l, [lp]) ->
        allocate (x, y) (w', h') scale clear l lp
       where
        (w', h') = preserveAspect (rw, rh) (w, h)
        (rw, rh) = reqSize props
      (LayoutScaleBy s l, [lp]) ->
        allocate (x, y) (w, h) (scale * s) clear l lp
      (LayoutScaleFit l, [lp]) ->
        allocate (x, y) (w, h) (scale * s) clear l lp
       where
        s =
          min
            (fromIntegral w' / fromIntegral rw)
            (fromIntegral h' / fromIntegral rh)
        (w', h') = preserveAspect (rw, rh) (w, h)
        (rw, rh) = reqSize props
      (LayoutAbove ls, _) ->
        concat
          [ allocate (x, y') (w, h') scale clear l lp
          | (y', h', l, lp) <- zip4 ys hs ls lps
          ]
       where
        rh = sum (map (snd . reqSize . Tree.rootLabel) lps)
        ys = scanl (+) y hs
        hs
          | h <= rh =
              takeUpTo h (map (snd . reqSize . Tree.rootLabel) lps)
          | otherwise =
              [ if expand
                then rh' + dh + (if i < dhrem then 1 else 0)
                else rh'
              | let ( nexpand
                      , iprops
                      ) = enumerateExpanding (map rootLabel lps)
                    extra = h - rh
                    (dh, dhrem) = divMod extra nexpand
              , ( i
                  , LayoutProps
                      { reqSize = (_rw', rh')
                      , expand
                      }
                  ) <-
                  iprops
              ]
      (LayoutBeside ls, _) ->
        concat
          [ allocate (x', y) (w', h) scale clear l lp
          | (x', w', l, lp) <- zip4 xs ws ls lps
          ]
       where
        rw = sum (map (fst . reqSize . Tree.rootLabel) lps)

        xs = scanl (+) x ws
        ws
          | w <= rw =
              takeUpTo w (map (fst . reqSize . Tree.rootLabel) lps)
          | otherwise =
              [ if expand
                then rw' + dw + (if i < dwrem then 1 else 0)
                else rw'
              | let ( nexpand
                      , iprops
                      ) = enumerateExpanding (map rootLabel lps)
                    extra = w - rw
                    (dw, dwrem) = divMod extra nexpand
              , ( i
                  , LayoutProps
                      { reqSize = (rw', _rh')
                      , expand
                      }
                  ) <-
                  iprops
              ]
      (LayoutOver [], []) -> []
      (LayoutOver (l : ls), lp : lps') ->
        concat $
          allocate (x, y) (w, h) scale clear l lp
            : [ allocate (x, y) (w, h) scale False l' lp'
              | (l', lp') <- zip ls lps'
              ]
      _ -> error "layoutTiles: inconsistent layout properties"

  -- enumerate all the elemets with expand=True, and count the number of them
  enumerateExpanding :: [LayoutProperties] -> (Int, [(Int, LayoutProperties)])
  enumerateExpanding =
    mapAccumL
      ( \i p ->
          let i'
                | expand p = i + 1
                | otherwise = i
           in (i', (i, p))
      )
      0

takeUpTo :: Int -> [Int] -> [Int]
takeUpTo n = go 0
 where
  go !_ [] = []
  go !a (x : xs)
    | a + x >= n = [x] -- inclusive
    | otherwise = x : go (a + x) xs

data LayoutProperties = LayoutProps
  { reqSize :: !(Int, Int)
  , expand :: !Bool
  }

-- | Collect the bottom-up layout properties: requested size and expansion.
layoutProperties ::
  forall a.
  (a -> (Int, Int)) ->
  Layout a ->
  Tree LayoutProperties
layoutProperties reqSizeBase =
  bottomUp
 where
  bottomUp :: Layout a -> Tree LayoutProperties
  bottomUp (Layout a) =
    Tree.Node
      LayoutProps
        { reqSize = reqSizeBase a
        , expand = True
        }
      []
  bottomUp (LayoutExpand l) =
    Tree.Node p{expand = True} [lp]
   where
    lp@(Tree.Node p _) = bottomUp l
  bottomUp (LayoutFixed l) =
    Tree.Node p{expand = False} [lp]
   where
    lp@(Tree.Node p _) = bottomUp l
  bottomUp (LayoutAspect l) =
    Tree.Node p [lp]
   where
    lp@(Tree.Node p _) = bottomUp l
  bottomUp (LayoutReqSize w h l) =
    Tree.Node p{reqSize = (w, h)} [lp]
   where
    lp@(Tree.Node p _) = bottomUp l
  bottomUp (LayoutScaleBy s l) =
    Tree.Node p{reqSize = (w', h')} [lp]
   where
    lp@(Tree.Node p@LayoutProps{reqSize = (w, h)} _) = bottomUp l
    w' = round (s * fromIntegral w)
    h' = round (s * fromIntegral h)
  bottomUp (LayoutScaleFit l) =
    Tree.Node p [lp]
   where
    lp@(Tree.Node p _) = bottomUp l
  bottomUp (LayoutAbove ls) = bottomUpAcc max (+) ls
  bottomUp (LayoutBeside ls) = bottomUpAcc (+) max ls
  bottomUp (LayoutOver ls) = bottomUpAcc (+) (+) ls

  bottomUpAcc accW accH ls =
    Tree.Node
      LayoutProps
        { reqSize =
            foldl1'
              ( \(aw, ah) (w', h') ->
                  let !aw' = accW aw w'
                      !ah' = accH ah h'
                   in (aw', ah')
              )
              [reqSize p | Tree.Node p _ <- props]
        , expand = or [expand p | Tree.Node p _ <- props]
        }
      props
   where
    props = map bottomUp ls

preserveAspect :: (Int, Int) -> (Int, Int) -> (Int, Int)
preserveAspect (reqX, reqY) (allocX, allocY)
  | allocX % allocY >= reqX % reqY =
      -- wider then taller, so use full allocation for height, and scale width
      let !allocX' =
            floor $
              toRational reqX
                * toRational allocY
                / toRational reqY
       in (allocX', allocY)
  | otherwise =
      -- taller than wide, so use full allocation for width, and scale height
      let !allocY' =
            floor $
              toRational reqY
                * toRational allocX
                / toRational reqX
       in (allocX, allocY')

renderTiles ::
  forall model.
  [LayoutTile (VizRender model)] ->
  Bool ->
  Time ->
  FrameNo ->
  model ->
  Cairo.Render ()
renderTiles tiles forceRender time frame model =
  sequence_
    [ when (shouldRender tile) $ renderTile tile
    | tile <- tiles
    ]
 where
  shouldRender (LayoutTile _ VizRender{renderChanged}) =
    forceRender || renderChanged time frame model

  renderTile :: LayoutTile (VizRender model) -> Cairo.Render ()
  renderTile (LayoutTile tile VizRender{renderModel}) =
    renderWithinTile tile $
      renderModel time frame model

  renderWithinTile ::
    Tile ->
    ((Double, Double) -> Cairo.Render ()) ->
    Cairo.Render ()
  renderWithinTile
    Tile
      { tileX
      , tileY
      , tileW
      , tileH
      , tileScale
      , tileClear
      }
    render = do
      Cairo.save
      Cairo.rectangle
        (fromIntegral tileX)
        (fromIntegral tileY)
        (fromIntegral tileW)
        (fromIntegral tileH)
      when tileClear $ do
        Cairo.setSourceRGB 1 1 1
        Cairo.fillPreserve
        Cairo.setSourceRGB 0 0 0
      Cairo.clip
      Cairo.translate (fromIntegral tileX) (fromIntegral tileY)
      if tileScale == 1.0
        then render (fromIntegral tileW, fromIntegral tileH)
        else do
          Cairo.scale tileScale tileScale
          render
            ( fromIntegral tileW / tileScale
            , fromIntegral tileH / tileScale
            )
      Cairo.restore

data GtkVizConfig = GtkVizConfig
  { gtkVizFPS :: Int
  , gtkVizResolution :: Maybe (Int, Int)
  , gtkVizCpuRendering :: Bool
  -- ^ If @True@, use client side CPU-based Cairo rendering. Otherwise
  -- use Gtk+ offscreen Cairo rendering, which may use GPU acceleration.
  --
  -- For X11-based desktops, the Gtk+ offscreen rendering may actually
  -- use more CPU time as it generates load on the X11 server, which
  -- may or may not itself use GPU acceleration.
  }

defaultGtkVizConfig :: GtkVizConfig
defaultGtkVizConfig =
  GtkVizConfig
    { gtkVizFPS = 25
    , gtkVizResolution = Nothing
    , gtkVizCpuRendering = False
    }

-- | Animate the vizualisation in a Gtk+ window.
vizualise :: GtkVizConfig -> Vizualisation -> IO ()
vizualise
  GtkVizConfig
    { gtkVizFPS
    , gtkVizResolution
    , gtkVizCpuRendering
    }
  (Viz vizmodel vizrender) = do
    _ <- Gtk.initGUI
    window <- Gtk.windowNew
    canvas <- Gtk.drawingAreaNew

    Gtk.set
      window
      [ Gtk.containerChild := canvas
      , Gtk.windowResizable := True
      , Gtk.windowTitle := ("Visualisation" :: String)
      ]
    let (width, height) =
          case gtkVizResolution of
            Just (w, h) -> (w, h)
            Nothing -> (w, h)
             where
              LayoutProps{reqSize = (w, h)} = rootLabel props
              props = layoutProperties renderReqSize vizrender
     in Gtk.windowSetDefaultSize window width height

    fullscreenRef <- newIORef False
    maximisedRef <- newIORef False
    _ <- Gtk.on window Gtk.windowStateEvent $ Gtk.tryEvent $ do
      state <- Gtk.eventWindowState
      liftIO $ writeIORef fullscreenRef (Gtk.WindowStateFullscreen `elem` state)
      liftIO $ writeIORef maximisedRef (Gtk.WindowStateMaximized `elem` state)
    let toggleFullscreen = do
          previouslyFullscreen <- readIORef fullscreenRef
          Gtk.set window [Gtk.windowDecorated := previouslyFullscreen]
          if previouslyFullscreen
            then Gtk.windowUnfullscreen window
            else Gtk.windowFullscreen window
        toggleMaximised = do
          previouslyFullscreen <- readIORef fullscreenRef
          previouslyMaximised <- readIORef maximisedRef
          case (previouslyFullscreen, previouslyMaximised) of
            (True, _) -> do
              Gtk.set window [Gtk.windowDecorated := True]
              Gtk.windowUnfullscreen window
              Gtk.windowMaximize window
            (False, True) -> Gtk.windowUnmaximize window
            (False, False) -> Gtk.windowMaximize window

    _ <- Gtk.on window Gtk.keyPressEvent $ Gtk.tryEvent $ do
      name <- Gtk.eventKeyName
      case name of
        "Escape" -> liftIO $ Gtk.widgetDestroy window
        "F11" -> liftIO toggleMaximised
        "F5" -> liftIO toggleFullscreen
        "f" -> liftIO toggleFullscreen
        _ -> return ()

    _ <- Gtk.on window Gtk.objectDestroy $ do
      liftIO Gtk.mainQuit

    -- The model state
    modelRef <- newIORef (stepModelInitial vizmodel)

    -- Iterate the model forward on a timer
    _ <- flip Gtk.timeoutAdd (1000 `div` gtkVizFPS) $ do
      (time, frameno, model) <- liftIO $ readIORef modelRef
      let (!time', !frameno', !model') =
            stepModelWithTime vizmodel gtkVizFPS (time, frameno, model)
      writeIORef modelRef (time', frameno', model')
      Gtk.widgetQueueDraw canvas
      return True

    -- The rendering state: an off-screen surface, and the layout tiles
    -- These both match the current size of the screen, which changes on
    -- the Gtk.configureEvent.
    renderRef <- newIORef Nothing

    _ <- Gtk.on canvas Gtk.configureEvent $ liftIO $ do
      mdrawwindow <- Gtk.widgetGetWindow canvas
      case mdrawwindow of
        Nothing -> fail "No draw window!"
        Just drawwindow -> do
          w <- Gtk.drawWindowGetWidth drawwindow
          h <- Gtk.drawWindowGetHeight drawwindow
          surface <-
            if gtkVizCpuRendering
              then Cairo.createImageSurface Cairo.FormatRGB24 w h
              else Gtk.renderWithDrawWindow drawwindow $
                Cairo.withTargetSurface $ \mainSurface ->
                  liftIO $
                    Cairo.createSimilarSurface
                      mainSurface
                      Cairo.ContentColor
                      w
                      h
          let props = layoutProperties renderReqSize vizrender
              viztiles = layoutTiles (w, h) vizrender props
          (time, frameno, model) <- readIORef modelRef
          Cairo.renderWith surface $ do
            Cairo.setSourceRGB 1 1 1
            Cairo.rectangle 0 0 (fromIntegral w) (fromIntegral h)
            Cairo.fill
            renderTiles viztiles True time frameno model
          writeIORef renderRef (Just (viztiles, surface))
      return True

    _ <- Gtk.on canvas Gtk.draw $ do
      renderState <- liftIO $ readIORef renderRef
      case renderState of
        Just (viztiles, surface) -> do
          (time, frameno, model) <- liftIO $ readIORef modelRef
          Cairo.renderWith surface $ do
            renderTiles viztiles False time frameno model
          Cairo.setSourceSurface surface 0 0
          Cairo.paint
        Nothing -> return ()

    Gtk.widgetShowAll window
    Gtk.mainGUI

data AnimVizConfig = AnimVizConfig
  { animVizFrameFiles :: Int -> FilePath
  , animVizDuration :: Int
  , animVizStartTime :: Int
  , animVizFPS :: Int
  , animVizResolution :: Maybe (Int, Int)
  }

defaultAnimVizConfig :: AnimVizConfig
defaultAnimVizConfig =
  AnimVizConfig
    { animVizFrameFiles = \n -> "viz-frame-" ++ show n ++ ".png"
    , animVizDuration = 60
    , animVizStartTime = 0
    , animVizFPS = 25
    , animVizResolution = Nothing
    }

-- | Write n seconds of animation frame files (at 25 fps) for the given
-- vizualisation.
--
-- To turn into a video, use a command like:
--
-- > ffmpeg -i example/frame-%d.png -vf format=yuv420p example.mp4
writeAnimationFrames :: AnimVizConfig -> Vizualisation -> IO ()
writeAnimationFrames
  AnimVizConfig
    { animVizFrameFiles = frameFilename
    , animVizDuration = runningtime
    , animVizStartTime = starttime
    , animVizFPS = fps
    , animVizResolution
    }
  (Viz vizmodel (vizrender :: Layout (VizRender model))) =
    let (time, frameno, model) = skipFrames (stepModelInitial vizmodel)
     in go time frameno model
   where
    frameStart = starttime * fps
    frameMax = frameStart + runningtime * fps

    props = layoutProperties renderReqSize vizrender
    viztiles = layoutTiles (width, height) vizrender props
    ( width
      , height
      ) = case animVizResolution of
        Just (w, h) -> (w, h)
        Nothing -> (w, h)
         where
          LayoutProps{reqSize = (w, h)} = rootLabel props

    skipFrames :: (Time, FrameNo, model) -> (Time, FrameNo, model)
    skipFrames (!time, !frameno, !model)
      | frameno >= frameStart =
          (time, frameno, model)
      | otherwise =
          skipFrames (stepModelWithTime vizmodel fps (time, frameno, model))

    go :: Time -> FrameNo -> model -> IO ()
    go _ !frameno _ | frameno >= frameMax = return ()
    go !time !frameno !model = do
      Cairo.withImageSurface Cairo.FormatRGB24 width height $ \surface -> do
        Cairo.renderWith surface $ do
          Cairo.rectangle 0 0 (fromIntegral width) (fromIntegral height)
          Cairo.setSourceRGB 1 1 1
          Cairo.fill
          renderTiles viztiles True time frameno model
        Cairo.surfaceWriteToPNG surface (frameFilename (frameno - frameStart))

      let (time', frameno', model') =
            stepModelWithTime vizmodel fps (time, frameno, model)

      go time' frameno' model'

nullVizModel :: VizModel ()
nullVizModel =
  VizModel
    { initModel = ()
    , stepModel = \_ _ _ () -> ()
    }

pairVizModel :: VizModel modela -> VizModel modelb -> VizModel (modela, modelb)
pairVizModel vizmodela vizmodelb =
  VizModel
    { initModel =
        ( initModel vizmodela
        , initModel vizmodelb
        )
    , stepModel = \dt t fn (ma, mb) ->
        ( stepModel vizmodela dt t fn ma
        , stepModel vizmodelb dt t fn mb
        )
    }

aboveVizualisation :: Vizualisation -> Vizualisation -> Vizualisation
aboveVizualisation
  (Viz vizmodela (vizrendera :: Layout (VizRender modela)))
  (Viz vizmodelb (vizrenderb :: Layout (VizRender modelb))) =
    Viz
      (pairVizModel vizmodela vizmodelb)
      ( LayoutAbove
          [ fmap (contramap fst) vizrendera
          , fmap (contramap snd) vizrenderb
          ]
      )

besideVizualisation :: Vizualisation -> Vizualisation -> Vizualisation
besideVizualisation
  (Viz vizmodela (vizrendera :: Layout (VizRender modela)))
  (Viz vizmodelb (vizrenderb :: Layout (VizRender modelb))) =
    Viz
      (pairVizModel vizmodela vizmodelb)
      ( LayoutBeside
          [ fmap (contramap fst) vizrendera
          , fmap (contramap snd) vizrenderb
          ]
      )

slowmoVizualisation :: DiffTime -> Vizualisation -> Vizualisation
slowmoVizualisation
  dilation
  (Viz vizmodel (vizrender :: Layout (VizRender model))) =
    Viz
      vizmodel
        { initModel = (Time 0, initModel vizmodel)
        , stepModel = stepModel'
        }
      (fmap adjustVizRenderTime vizrender)
   where
    stepModel' ::
      DiffTime ->
      Time ->
      FrameNo ->
      (Time, model) ->
      (Time, model)
    stepModel' delta (Time now) frameno (_now, m) =
      (now', stepModel vizmodel delta' now' frameno m)
     where
      delta' :: DiffTime
      delta' = delta * dilation

      now' :: Time
      now' = Time (now * dilation)

    adjustVizRenderTime :: VizRender model -> VizRender (Time, model)
    adjustVizRenderTime vr@VizRender{renderChanged, renderModel} =
      vr
        { renderChanged = \_t fn (t, m) -> renderChanged t fn m
        , renderModel = \_t fn (t, m) -> renderModel t fn m
        }

nullVizRender :: VizRender model
nullVizRender =
  VizRender
    { renderReqSize = (4, 0)
    , renderChanged = \_t _fn _ -> False
    , renderModel = \_t _fn _m _s -> return ()
    }

layoutLabelTime :: Layout (VizRender model)
layoutLabelTime =
  LayoutFixed $
    Layout
      VizRender
        { renderReqSize = (400, 20)
        , renderChanged = \_t _fn _ -> True
        , renderModel
        }
 where
  renderModel :: Time -> FrameNo -> model -> (Double, Double) -> Cairo.Render ()
  renderModel (Time t) _fn _m (_w, _h) = do
    Cairo.moveTo 5 20
    Cairo.setFontSize 20
    Cairo.setSourceRGB 0 0 0
    Cairo.showText $
      Time.formatTime Time.defaultTimeLocale "Time (sec): %-2Es" t

layoutLabel :: Int -> String -> Layout (VizRender model)
layoutLabel size label =
  LayoutFixed $
    Layout
      VizRender
        { renderReqSize = (400, size + 12)
        , renderChanged = \_t _fn _ -> False
        , renderModel = \_t _fn _m (w, _h) -> do
            layout <- liftIO $ do
              ctx <- Pango.cairoCreateContext Nothing
              layout <- Pango.layoutEmpty ctx
              font <- Pango.fontDescriptionNew
              Pango.fontDescriptionSetFamily font ("Sans" :: String)
              Pango.fontDescriptionSetSize font (fromIntegral size)
              Pango.layoutSetFontDescription layout (Just font)
              Pango.layoutSetWidth layout (Just w)
              Pango.layoutSetWrap layout Pango.WrapWholeWords
              Pango.layoutSetEllipsize layout Pango.EllipsizeEnd
              Pango.layoutSetAlignment layout Pango.AlignCenter
              Pango.layoutSetText layout label
              return layout
            Cairo.moveTo 0 0
            Pango.showLayout layout
        }
