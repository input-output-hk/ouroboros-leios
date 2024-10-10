-- | This module list all available `Vizualisation`
--
-- Should you add a new `Vizualisation`, you should add it here as well.
module VizName where

import Data.Char (isSpace)
import qualified ExamplesRelay
import qualified ExamplesRelayP2P
import qualified ExamplesTCP
import Test.QuickCheck (Arbitrary (..), arbitraryBoundedEnum)
import Viz (Vizualisation)

data VizName
  = VizTCP1
  | VizTCP2
  | VizTCP3
  | VizRelay1
  | VizRelay2
  | VizRelayP2P1
  | VizRelayP2P2
  deriving (Eq, Enum, Bounded)

instance Arbitrary VizName where
  arbitrary = arbitraryBoundedEnum

instance Show VizName where
  show VizTCP1 = "tcp-1"
  show VizTCP2 = "tcp-2"
  show VizTCP3 = "tcp-3"
  show VizRelay1 = "relay-1"
  show VizRelay2 = "relay-2"
  show VizRelayP2P1 = "p2p-1"
  show VizRelayP2P2 = "p2p-2"

instance Read VizName where
  readsPrec _ s = case readVizName s of
    Right v -> [(v, "")]
    Left _ -> []
   where
    readVizName :: String -> Either String VizName
    readVizName input =
      case dropWhile isSpace input of
        "tcp-1" -> Right VizTCP1
        "tcp-2" -> Right VizTCP2
        "tcp-3" -> Right VizTCP3
        "relay-1" -> Right VizRelay1
        "relay-2" -> Right VizRelay2
        "p2p-1" -> Right VizRelayP2P1
        "p2p-2" -> Right VizRelayP2P2
        _ -> Left "unknown vizualisation"

namedViz :: VizName -> Vizualisation
namedViz VizTCP1 = ExamplesTCP.example1
namedViz VizTCP2 = ExamplesTCP.example2
namedViz VizTCP3 = ExamplesTCP.example3
namedViz VizRelay1 = ExamplesRelay.example1
namedViz VizRelay2 = ExamplesRelay.example2
namedViz VizRelayP2P1 = ExamplesRelayP2P.example1
namedViz VizRelayP2P2 = ExamplesRelayP2P.example2
