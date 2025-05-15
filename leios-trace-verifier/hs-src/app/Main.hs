{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad (unless)
import Data.ByteString.Lazy as BSL
import Data.Map
import Data.Yaml
import LeiosConfig (Config (..))
import LeiosEvents
import LeiosTopology (LocationKind (..), Node (..), NodeInfo (..), NodeName (..), Topology (..))
import Lib
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import qualified Data.Text as T (unpack)

main :: IO ()
main =
  do
    Command{..} <- execParser commandParser
    (top :: Topology COORD2D) <- decodeFileThrow topologyFile
    (config :: Config) <- decodeFileThrow configFile
    let nrNodes = toInteger $ Prelude.length (elems $ nodes top)
    let nodeNames = Prelude.map unNodeName (keys $ nodes top)
    let stakes = Prelude.map (toInteger . stake . nodeInfo) (elems $ nodes top)
    let stakeDistribution = Prelude.zip nodeNames stakes
    let stageLength = toInteger (leiosStageLengthSlots config)
    result <-
      verifyTrace nrNodes idSut stakeDistribution stageLength
        . decodeJSONL
        <$> BSL.readFile logFile
    hPutStrLn stderr $ "Applying " <> show (fst result) <> " actions"
    unless (snd result == "ok")
      $ do
        putStrLn . T.unpack $ snd result
        exitFailure

data Command = Command
  { logFile :: FilePath
  , configFile :: FilePath
  , topologyFile :: FilePath
  , idSut :: Integer
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: ParserInfo Command
commandParser =
  info (com <**> helper) $
    fullDesc
      <> progDesc "Leios trace verifier"
      <> header "parser - a Leios trace verifier"
 where
  com =
    Command
      <$> strOption (long "trace-file" <> help "Short Leios simulation trace log file")
      <*> strOption (long "config-file" <> help "Short Leios configuration file")
      <*> strOption (long "topology-file" <> help "Short Leios topology file")
      <*> option auto (long "idSut" <> help "Id of system under test (SUT)")
