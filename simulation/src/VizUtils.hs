{-# LANGUAGE BangPatterns #-}

module VizUtils where

import qualified Graphics.Rendering.Cairo as Cairo

--
-- Cairo rendering utils
--

renderPathRoundedRect :: (Double, Double)
                      -> (Double, Double)
                      -> Double
                      -> Cairo.Render ()
renderPathRoundedRect a@(x1,_) b@(x2,_) w = do
    if (x2 > x1)
      then uncurry Cairo.arc a' r ( π/2+α) (-π/2+α)
      else uncurry Cairo.arc a' r (-π/2+α) ( π/2+α)
    if (x2 > x1)
      then uncurry Cairo.arc b' r (-π/2+α) ( π/2+α)
      else uncurry Cairo.arc b' r ( π/2+α) (-π/2+α)
    Cairo.closePath
  where
    π  = pi
    α  = angleV v
    v  = vector a b
    uv = unitV v
    a' = a `addV` scaleV   r  uv
    b' = b `addV` scaleV (-r) uv
    r  = w/2

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

vector :: (Double, Double) -> (Double, Double) -> (Double, Double)
vector (x0, y0) (x1, y1) = (x1 - x0, y1 - y0)

addV :: (Double, Double) -> (Double, Double) -> (Double, Double)
addV (x0, y0) (x1, y1) = (x0 + x1, y0 + y1)

negateV :: (Double, Double) -> (Double, Double)
negateV (dx, dy) = (-dx, -dy)

lenV :: (Double, Double) -> Double
lenV (dx, dy) = sqrt (dx^(2::Int) + dy^(2::Int))

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

angleV :: (Double, Double) -> Double
angleV (x,y) = atan (y / x)

midpointV :: (Double, Double) -> (Double, Double) -> (Double, Double)
midpointV a b = scaleV 0.5 (addV a b)

-- | Given the world size, world position, and screen size, return the
-- position in screen coordinates.
--
simPointToPixel :: (Double, Double) -- ^ Sim world dimensions
                -> (Double, Double) -- ^ Screen size
                -> (Double, Double) -- ^ Sim world position
                -> (Double, Double) -- ^ Screen coordinates
simPointToPixel (!ww, !wh) (!sw, !sh) (!wx, !wy) = (sx, sy)
  where
    !sx = wx/ww * sw
    !sy = wy/wh * sh
