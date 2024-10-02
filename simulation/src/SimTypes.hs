module SimTypes where

import Data.Ix (Ix)

newtype NodeId = NodeId Int
  deriving (Eq, Ord, Ix, Show)

data LabelNode e = LabelNode NodeId e deriving (Show)
data LabelLink e = LabelLink NodeId NodeId e deriving (Show)

-- | Position in simulation world coordinates
data Point = Point !Double !Double deriving (Show)

data WorldShape = WorldShape
  { worldDimensions :: !(Double, Double)
  -- ^ The dimensions of the world in simulation world coordinates
  -- (Circumference, pole-to-pole)
  , worldIsCylinder :: !Bool
  -- ^ If the world is a cylinder, and so wraps around from the East edge
  -- to the West edge, or if the world is a rectangle, with no wrapping at
  -- the edges. This affects the latencies.
  }
  deriving (Show)
