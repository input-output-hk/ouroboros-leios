{-# LANGUAGE BangPatterns #-}

module VizUtils where

import Data.Word (Word8)
import qualified Graphics.Rendering.Cairo as Cairo
import SimTypes (Point (..))
import System.Random (StdGen, uniform)

data Vector = Vector !Double !Double

--
-- Cairo rendering utils
--

withPoint :: (Double -> Double -> a) -> Point -> a
withPoint f (Point x y) = f x y

renderPathRoundedRect :: Point -> Point -> Double -> Cairo.Render ()
renderPathRoundedRect a@(Point x1 _) b@(Point x2 _) w = do
  if x2 > x1
    then withPoint Cairo.arc a' r (π / 2 + α) ((-π) / 2 + α)
    else withPoint Cairo.arc a' r ((-π) / 2 + α) (π / 2 + α)
  if x2 > x1
    then withPoint Cairo.arc b' r ((-π) / 2 + α) (π / 2 + α)
    else withPoint Cairo.arc b' r (π / 2 + α) ((-π) / 2 + α)
  Cairo.closePath
 where
  π = pi
  α = angleV v
  v = vector a b
  uv = unitV v
  a' = a `addP` scaleV r uv
  b' = b `addP` scaleV (-r) uv
  r = w / 2

translateLineNormal ::
  Double ->
  (Point, Point) ->
  (Point, Point)
translateLineNormal displace (a, b) =
  (a', b')
 where
  a' = addP a d
  b' = addP b d
  d = scaleV displace (normalV uv)
  uv = unitV v
  v = vector a b

vector :: Point -> Point -> Vector
vector (Point x0 y0) (Point x1 y1) = Vector (x1 - x0) (y1 - y0)

addP :: Point -> Vector -> Point
addP (Point x0 y0) (Vector x1 y1) = Point (x0 + x1) (y0 + y1)

addV :: Vector -> Vector -> Vector
addV (Vector x0 y0) (Vector x1 y1) = Vector (x0 + x1) (y0 + y1)

negateV :: Vector -> Vector
negateV (Vector dx dy) = Vector (-dx) (-dy)

lenV :: Vector -> Double
lenV (Vector dx dy) = sqrt (dx ^ (2 :: Int) + dy ^ (2 :: Int))

normalV :: Vector -> Vector
normalV (Vector dx dy) = Vector (-dy) dx

normalV' :: Vector -> Vector
normalV' (Vector dx dy) = Vector dy (-dx)

unitV :: Vector -> Vector
unitV (Vector dx dy) = Vector (dx / l) (dy / l)
 where
  l = lenV (Vector dx dy)

scaleV :: Double -> Vector -> Vector
scaleV s (Vector dx dy) = Vector (dx * s) (dy * s)

angleV :: Vector -> Double
angleV (Vector x y) = atan (y / x)

midpointP :: Point -> Point -> Point
midpointP (Point x0 y0) (Point x1 y1) = Point ((x0 + x1) / 2) ((y0 + y1) / 2)

-- | Given the world size, world position, and screen size, return the
-- position in screen coordinates.
simPointToPixel ::
  -- | Sim world dimensions
  (Double, Double) ->
  -- | Screen size
  (Double, Double) ->
  -- | Sim world position
  Point ->
  -- | Screen coordinates
  Point
simPointToPixel (!ww, !wh) (!sw, !sh) (Point wx wy) = Point sx sy
 where
  !sx = wx / ww * sw
  !sy = wy / wh * sh

rngColor :: StdGen -> (Double, Double, Double)
rngColor rng = (fromIntegral r / 256, fromIntegral g / 256, fromIntegral b / 256)
 where
  r, g, b :: Word8
  ((r, g, b), _) = uniform rng
