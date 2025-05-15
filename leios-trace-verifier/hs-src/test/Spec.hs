{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Paths_trace_parser as Paths
import Control.Monad (forM_)
import Data.ByteString.Lazy as BSL (readFile)
import Data.List (sort)
import Data.Map (elems, keys)
import Data.Text (Text)
import Data.Yaml (decodeFileThrow)
import LeiosConfig (Config (..))
import LeiosEvents (decodeJSONL)
import LeiosTopology (LocationKind (COORD2D), Node (..), NodeInfo (..), NodeName (..), Topology (..))
import Lib (verifyTrace)
import System.Directory (listDirectory)
import System.FilePath ((</>))
import Test.Hspec (Expectation, SpecWith, describe, hspec, it, shouldBe, shouldNotBe)

main :: IO ()
main = do
  dir <- Paths.getDataDir
  validFiles <- sort <$> listDirectory (dir </> "valid")
  invalidFiles <- sort <$> listDirectory (dir </> "invalid")
  (top :: Topology COORD2D) <- decodeFileThrow (dir </> "topology.yaml")
  (config :: Config) <- decodeFileThrow (dir </> "config.yaml")
  let nrNodes = toInteger $ Prelude.length (elems $ nodes top)
  let nodeNames = Prelude.map unNodeName (keys $ nodes top)
  let stakes = Prelude.map (toInteger . stake . nodeInfo) (elems $ nodes top)
  let stakeDistribution = Prelude.zip nodeNames stakes
  let stageLength = toInteger (leiosStageLengthSlots config)
  let idSut = 0
  let check :: String -> String -> [FilePath] -> (Text -> Text -> Expectation) -> SpecWith ()
      check label folder files predicate =
        describe label $ do
          forM_ files $ \file ->
            it file $ do
              result <-
                verifyTrace nrNodes idSut stakeDistribution stageLength
                  . decodeJSONL
                  <$> BSL.readFile (dir </> folder </> file)
              snd result `predicate` "ok"
  hspec $ do
    check "Verify valid traces" "valid" validFiles shouldBe
    check "Reject invalid traces" "invalid" invalidFiles shouldNotBe
