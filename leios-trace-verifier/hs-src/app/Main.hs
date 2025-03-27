{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Data.ByteString.Lazy as BSL
import Data.Map
import Data.Yaml
import LeiosEvents
import LeiosTopology
import Lib
import Options.Applicative

main :: IO ()
main =
  do
    Command{..} <- execParser commandParser
    (top :: Topology CLUSTER) <- decodeFileThrow topologyFile
    let nrNodes = toInteger $ Prelude.length $ elems $ nodes top
    BSL.readFile logFile >>= print . verifyTrace nrNodes idSut . decodeJSONL

data Command = Command
  { logFile :: FilePath
  , topologyFile :: FilePath
  , idSut :: Integer
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: ParserInfo Command
commandParser =
  info (com <**> helper) $
    fullDesc
      <> progDesc "Short Leios trace verifier"
      <> header "parser - a Short Leios trace verifier"
 where
  com =
    Command
      <$> strOption (long "trace-file" <> help "Short Leios simulation trace log file")
      <*> strOption (long "topology-file" <> help "Short Leios topology file")
      <*> option auto (long "idSut" <> help "Id of system under test (SUT)")
