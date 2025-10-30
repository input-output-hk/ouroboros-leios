{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Golden tests.
module Spec.Golden (
  golden,
) where

import Control.Monad (forM_)
import Data.ByteString.Lazy as BSL (readFile)
import Data.List (sort)
import Data.Map (elems, keys)
import Data.Text (Text)
import Data.Yaml (decodeFileThrow)
import LeiosConfig (Config (..))
import LeiosEvents (decodeJSONL)
import LeiosTopology (LocationKind (COORD2D), Node (..), NodeInfo (..), NodeName (..), Topology (..))
import qualified Paths_trace_parser as Paths
import ShortLeiosLib (verifyTrace)
import System.Directory (listDirectory)
import System.FilePath ((</>))
import Test.Hspec (Expectation, Spec, SpecWith, describe, it, runIO, shouldBe, shouldNotBe)

-- | Run golden tests.
golden :: Spec
golden = do
  dir <- runIO $ Paths.getDataDir
  validFiles <- runIO $ sort <$> listDirectory (dir </> "valid")
  invalidFiles <- runIO $ sort <$> listDirectory (dir </> "invalid")
  (top :: Topology COORD2D) <- runIO $ decodeFileThrow (dir </> "topology.yaml")
  (config :: Config) <- runIO $ decodeFileThrow (dir </> "config.yaml")
  let nrNodes = toInteger $ Prelude.length (elems $ nodes top)
  let nodeNames = Prelude.map unNodeName (keys $ nodes top)
  let stakes = Prelude.map (toInteger . stake . nodeInfo) (elems $ nodes top)
  let stakeDistribution = Prelude.zip nodeNames stakes
  let stageLength = toInteger (leiosStageLengthSlots config)
  let idSut = 0
  let ledgerQuality = ceiling (praosChainQuality config) -- TODO: int in schema?
  let lateIBInclusion = leiosLateIbInclusion config
  let check :: String -> String -> [FilePath] -> (Text -> Text -> Expectation) -> SpecWith ()
      check label folder files predicate =
        describe label $ do
          forM_ files $ \file ->
            it file $ do
              result <-
                verifyTrace nrNodes idSut stakeDistribution stageLength ledgerQuality lateIBInclusion
                  . decodeJSONL
                  <$> BSL.readFile (dir </> folder </> file)
              fst (snd result) `predicate` "ok"
  check "Verify valid traces" "valid" validFiles shouldBe
  check "Reject invalid traces" "invalid" invalidFiles shouldNotBe
