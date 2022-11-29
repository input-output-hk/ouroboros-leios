module SimTypes where

import Data.Ix (Ix)

newtype NodeId = NodeId Int
  deriving (Eq, Ord, Ix, Show)

data LabelNode e = LabelNode NodeId        e  deriving Show
data LabelLink e = LabelLink NodeId NodeId e  deriving Show

-- | Position in simulation world coordinates
--
data Point = Point !Double !Double deriving Show

data WorldShape = WorldShape {
       -- | The dimensions of the world in simulation world coordinates
       -- (Circumference, pole-to-pole)
       worldDimensions :: !(Double, Double)
     }
  deriving (Show)

