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
import LinearLeiosLib
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import qualified Data.Text as T (unpack)

main :: IO ()
main =
  do
    Command{..} <- execParser commandParser

    -- Parameters from topology
    (top :: Topology COORD2D) <- decodeFileThrow topologyFile
    let nrNodes = toInteger $ Prelude.length (elems $ nodes top)
    let nodeNames = Prelude.map unNodeName (keys $ nodes top)
    let stakes = Prelude.map (toInteger . stake . nodeInfo) (elems $ nodes top)
    let stakeDistribution = Prelude.zip nodeNames stakes

    -- Parameters from config
    (config :: Config) <- decodeFileThrow configFile
    let lhdr = 1 -- TODO: read from config
    let lvote = toInteger (linearVoteStageLengthSlots config)
    let ldiff = toInteger (linearDiffuseStageLengthSlots config)
    let validityCheckTime = 3 -- TODO: read from config
    result <-
      pure ($ startingSlot)
        <*> verifyTraceFromSlot nrNodes idSut stakeDistribution lhdr lvote ldiff validityCheckTime
            . decodeJSONL
            <$> BSL.readFile logFile
    hPutStrLn stderr $ "Applying " <> show (fst result) <> " actions"
    unless (fst (snd result) == "ok") $
      do
        putStrLn . T.unpack $ fst (snd result)
        putStrLn . T.unpack $ snd (snd result)
        exitFailure

data Command = Command
  { logFile :: FilePath
  , configFile :: FilePath
  , topologyFile :: FilePath
  , startingSlot :: Integer
  , idSut :: Integer
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: ParserInfo Command
commandParser =
  info (com <**> helper) $
    fullDesc
      <> progDesc "Linear Leios trace verifier"
      <> header "Leios trace verifier"
 where
  com =
    Command
      <$> strOption (long "trace-file" <> help "Leios simulation trace log file")
      <*> strOption (long "config-file" <> help "Leios configuration file")
      <*> strOption (long "topology-file" <> help "Leios topology file")
      <*> option auto (long "starting-slot" <> value 0 <> help "Starting slot of trace-file")
      <*> option auto (long "idSut" <> help "Id of system under test (SUT)")
