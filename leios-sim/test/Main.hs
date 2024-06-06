{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import qualified Data.Map as Map
import GHC.Natural (Natural)
import Network.FFD (Network (..), NetworkParameters (..))
import Node.Types (EndorsementBlock, Node, initializeNode)
import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec $ do
  describe "Simple network" $ do
    it "produces an EB given some IBs" $ do
      load <- defaultGenerator
      controller <- defaultController $ Bandwidth 10
      sut <- initializeNode defaultNodeParameters
      nodeOutput <- runNetwork defaultNetworkParameters load controller sut
      -- without bounds on the flow of traffic, all input IBs should end up in an EB      )
      length (ebs nodeOutput) `shouldNotBe` 0 -- provided >0 IBs were put in and enough time has passed
 where
  defaultGenerator :: IO Generator
  defaultGenerator = undefined
  defaultController :: Bandwidth -> IO Controller
  defaultController bandwidth = undefined
  defaultNodeParameters = undefined
  defaultNetworkParameters = undefined

runNetwork :: NetworkParameters -> Generator -> Controller -> Node -> IO NodeOutput
runNetwork nwParams gen ctrlr node = undefined
 where
  initialNetwork =
    Network
      { headers = Map.empty
      , bodies = Map.empty
      , prefHdr = Map.empty
      , currentTime = 0
      , sutOutput = []
      , params = nwParams
      }

data NodeOutput = NodeOutput
  { ebs :: [EndorsementBlock]
  }
data Generator = Generator
data Controller = Controller
newtype Bandwidth = Bandwidth Natural
  deriving newtype (Eq, Show, Num)
