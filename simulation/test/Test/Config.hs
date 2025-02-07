{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Test.Config where

import Control.Exception
import Data.Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Bifunctor (Bifunctor (..))
import Data.Default
import qualified Data.Text as T
import qualified Data.Yaml as Yaml
import JSONCompat
import LeiosProtocol.Config
import Paths_ouroboros_leios_sim (getDataFileName)
import SimTypes (World (..), WorldDimensions, WorldShape (..))
import System.Directory (doesFileExist)
import Test.QuickCheck (Arbitrary (..), Gen, NonNegative (..), Positive (..), Property, ioProperty)
import Test.QuickCheck.Arbitrary (arbitraryBoundedEnum)
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.Random (QCGen (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck (Small (..), testProperty)

tests :: TestTree
tests =
  testGroup
    "Config"
    [ testCaseSteps "test_defaultConfigOnDiskMatchesDef" test_defaultConfigOnDiskMatchesDef
    ]

test_defaultConfigOnDiskMatchesDef :: (String -> IO ()) -> Assertion
test_defaultConfigOnDiskMatchesDef step = do
  step "Checking default config file exists."
  defaultConfigFile <- getDataFileName "test/data/simulation/config.default.yaml"
  assertBool (unwords ["File", defaultConfigFile, "does not exist"]) =<< doesFileExist defaultConfigFile

  step $ unwords ["Attempting to read default config file: ", defaultConfigFile]
  diskConfig <- readConfig defaultConfigFile

  step "Checking on-disk config matches def."
  let defConfig = def :: Config
      diffJSONObjects (Object km) (Object km1) =
        Object
          ( KM.map snd . KM.filter (not . fst) $
              KM.intersectionWith (\l r -> (l == r, toJSON [l, r])) km km1
          )
      diffJSONObjects _ _ = String (T.pack "Not objects")
  assertEqual
    (unlines ["Default config file does not match Default.def", "diff:", show $ diffJSONObjects (toJSON defConfig) (toJSON diskConfig)])
    defConfig
    diskConfig

  step "Checking all the keys in def are also on disk."
  diskConfigValue <- Yaml.decodeFileEither defaultConfigFile
  case (toJSON defConfig, diskConfigValue) of
    (Object defKM, Right (Object diskKM)) -> do
      let diff = defKM `KM.difference` diskKM
      assertBool (unwords ["Config parameters missing on disk", show (map fst . KM.toList $ diff)]) $ (null diff)
    (_, Left err) -> assertFailure $ "Config not yaml: " ++ displayException err
    _otherwise -> assertFailure "Config not an Object."
