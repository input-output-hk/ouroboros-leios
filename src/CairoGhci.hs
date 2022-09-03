module CairoGhci where

import Data.IORef
import Control.Monad
import Control.Monad.IO.Class (liftIO)

-- Example of an drawing graphics onto a canvas.
import Graphics.UI.Gtk as Gtk
import Graphics.Rendering.Cairo as Cairo hiding (RectangleInt(..))
import Graphics.UI.Gtk.Gdk.EventM

import qualified Graphics.Rendering.Chart.Easy as Chart
import           Graphics.Rendering.Chart.Easy ((.=))
import qualified Graphics.Rendering.Chart.Backend.Cairo as Chart


run :: Render () -> IO ()
run act = do
    initGUI
    window <- windowNew
    canvas <- drawingAreaNew

    set window
      [ containerChild  := canvas
      , windowResizable := True
--      , widgetAppPaintable := True
      ]
    windowSetDefaultSize window 500 500

    on window objectDestroy $ do
      liftIO mainQuit

    backgroundRef <- newIORef Nothing
    on canvas configureEvent $ liftIO $ do
      print "Configure!"
      mbwindow <- widgetGetWindow canvas
      case mbwindow of
        Nothing -> print "No draw window!"
        Just win -> do
          print "Got draw window!"
          w <- drawWindowGetWidth  win
          h <- drawWindowGetHeight win
          print (w,h)
          background <- Gtk.renderWithDrawWindow win $
            withTargetSurface $ \mainSurface ->
               liftIO $ createSimilarSurface mainSurface ContentColor w h
          renderWith background $ do
            setSourceRGB 1 1 1
            Cairo.rectangle 0 0 (fromIntegral w) (fromIntegral h)
            fill
            setSourceRGB 0 0 0
            act
          liftIO $ writeIORef backgroundRef (Just background)
          print "Render!"
{-
      oldbackground <- readIORef backgroundRef
      case oldbackground of
        Nothing -> return ()
        Just background -> do
          print "Discarding old background!"
          surfaceFinish background
      writeIORef backgroundRef Nothing
-}
      return True

    on canvas draw $ do
      mbackground <- liftIO $ readIORef backgroundRef
      case mbackground of
        Just background -> do
          liftIO $ print "Paint!"
          setSourceSurface background 0 0
          paint
        Nothing -> return ()
{-
      background <- do
         mbbackground <- liftIO $ readIORef backgroundRef
         case mbbackground of
           Just background -> do
             liftIO $ print "Cached draw!"
             return background
           Nothing -> do
             liftIO $ print "Draw!"
             w <- liftIO $ widgetGetAllocatedWidth  canvas
             h <- liftIO $ widgetGetAllocatedHeight canvas
             background <- withTargetSurface $ \mainSurface ->
               liftIO $ createSimilarSurface mainSurface ContentColor w h
             renderWith background $ do
               setSourceRGB 1 1 1
               Cairo.rectangle 0 0 (fromIntegral w) (fromIntegral h)
               fill
               setSourceRGB 0 0 0
               act
             liftIO $ writeIORef backgroundRef (Just background)
             return background
      setSourceSurface background 0 0
      paint

    Gtk.timeoutAdd
      (Gtk.widgetQueueDraw canvas >> return True)
      (1000 `div` 25)
-}

    widgetShowAll window
    mainGUI

drawPipe :: (Double, Double) -> (Double, Double) -> Double -> Render ()
drawPipe a@(x1,_) b@(x2,_) r = do
    save
    if (x2 > x1)
      then uncurry arc a' r ( π/2+α) (-π/2+α)
      else uncurry arc a' r (-π/2+α) ( π/2+α)
    if (x2 > x1)
      then uncurry arc b' r (-π/2+α) ( π/2+α)
      else uncurry arc b' r ( π/2+α) (-π/2+α)
    closePath
    setSourceRGB 0.8 0.8 0.8
    fillPreserve
    setLineWidth 4
    setSourceRGB 0 0 0
    stroke
    uncurry moveTo a
    uncurry lineTo b
    stroke
    restore
  where
    π  = pi
    α  = angleV v
    v  = vector a b
    uv = unitV v
    a' = a `addV` scaleV   r  uv
    b' = b `addV` scaleV (-r) uv

drawCurve :: (Double, Double)
          -> (Double, Double)
          -> (Double, Double)
          -> (Double, Double)
          -> Render ()
drawCurve (x0, y0) (x1, y1) (x2, y2) (x3, y3) = do
  moveTo  x0 y0
  curveTo x1 y1 x2 y2 x3 y3
  setLineWidth 10
  setSourceRGB 0 0 0
  stroke
  moveTo x0 y0
  lineTo x1 y1
  moveTo x2 y2
  lineTo x3 y3
  setSourceRGBA 1 0 0 0.5
  setLineWidth 6
  stroke

drawRoundedRects :: (Double, Double)
                 -> (Double, Double)
                 -> Double
                 -> Render ()
drawRoundedRects a b w = do
    drawRoundedRect a1 b1 w
    drawRoundedRect a2 b2 w
  where
    (a1, b1) = translateLineNormal ( w/2) (a, b)
    (a2, b2) = translateLineNormal (-w/2) (a, b)

drawRoundedRect :: (Double, Double)
                -> (Double, Double)
                -> Double
                -> Render ()
drawRoundedRect a b w = do
    uncurry moveTo a0
    curveTo (fst a1) (snd a1) (fst a2) (snd a2) (fst a3) (snd a3)
    uncurry lineTo b0
    curveTo (fst b1) (snd b1) (fst b2) (snd b2) (fst b3) (snd b3)
    closePath
    stroke
    uncurry moveTo a
    uncurry lineTo b
    stroke
  where
    v   = vector a b
    uv  = unitV v

    a0 = a  `addV` scaleV (-w/2) (normalV uv)
    a1 = a0 `addV` scaleV (-w/1.5) uv
    a2 = a3 `addV` scaleV (-w/1.5) uv
    a3 = a  `addV` scaleV ( w/2) (normalV uv)

    b0 = b  `addV` scaleV ( w/2) (normalV uv)
    b1 = b0 `addV` scaleV ( w/1.5) uv
    b2 = b3 `addV` scaleV ( w/1.5) uv
    b3 = b  `addV` scaleV (-w/2) (normalV uv)

vector :: (Double, Double) -> (Double, Double) -> (Double, Double)
vector (x0, y0) (x1, y1) = (x1 - x0, y1 - y0)

addV :: (Double, Double) -> (Double, Double) -> (Double, Double)
addV (x0, y0) (x1, y1) = (x0 + x1, y0 + y1)

negateV :: (Double, Double) -> (Double, Double)
negateV (dx, dy) = (-dx, -dy)

lenV :: (Double, Double) -> Double
lenV (dx, dy) = sqrt (dx^2 + dy^2)

normalV :: (Double, Double) -> (Double, Double)
normalV (dx, dy) = (-dy, dx)

normalV' :: (Double, Double) -> (Double, Double)
normalV' (dx, dy) = ( dy,-dx)

unitV :: (Double, Double) -> (Double, Double)
unitV (dx, dy) = (dx / l, dy / l)
  where
    l = lenV (dx, dy)

scaleV :: Double -> (Double, Double) -> (Double, Double)
scaleV s (dx, dy) = (dx * s, dy * s)

angleV (x,y) = atan (y / x)

translateLineNormal :: Double
                    -> ((Double, Double), (Double, Double))
                    -> ((Double, Double), (Double, Double))
translateLineNormal displace (a, b) =
    (a', b')
  where
    a' = addV a d
    b' = addV b d
    d  = scaleV displace (normalV uv)
    uv = unitV v
    v  = vector a b



setRed :: Render ()
setRed = do
  setSourceRGB 1 0 0



setFat :: Render ()
setFat = do
  setLineWidth 20
  setLineCap LineCapRound



drawSquare :: Double -> Double -> Render ()
drawSquare width height = do
  (x,y) <- getCurrentPoint
  lineTo (x+width) y
  lineTo (x+width) (y+height)
  lineTo x (y+height)
  closePath
  stroke



drawHCirc :: Double -> Double -> Double -> Render ()
drawHCirc x y radius = do
  arc x y radius 0 pi
  stroke



drawStr :: String -> Render ()
drawStr txt = do
  lay <- createLayout txt
  showLayout lay



drawStr_ :: String -> Render ()
drawStr_ txt = do
  lay <- liftIO $ do
    ctxt <- cairoCreateContext Nothing
    descr <- contextGetFontDescription ctxt
    descr `fontDescriptionSetSize` 20
    ctxt `contextSetFontDescription` descr
    layoutText ctxt txt
  showLayout lay

chart1 :: (Double, Double) -> Render ()
chart1 dims =
    renderChart dims chart
  where
    signal :: [Double] -> [(Double,Double)]
    signal xs = [ (x,(sin (x*3.14159/45) + 1) / 2 * (sin (x*3.14159/5))) | x <- xs ]

    chart :: Chart.EC (Chart.Layout Double Double) ()
    chart = do
      Chart.layout_title .= "Amplitude Modulation"
      Chart.setColors [Chart.opaque Chart.blue, Chart.opaque Chart.red]
      Chart.plot (Chart.line "am" [signal [0,(0.5)..400]])
      Chart.plot (Chart.points "am points" (signal [0,7..400]))
      return ()

renderChart :: (Chart.Default r, Chart.ToRenderable r)
            => (Double, Double) -> Chart.EC r () -> Render ()
renderChart (width, height) =
    void
  . Chart.runBackend (Chart.defaultEnv Chart.bitmapAlignmentFns)
  . flip Chart.render (width, height)
  . Chart.toRenderable
  . Chart.execEC

