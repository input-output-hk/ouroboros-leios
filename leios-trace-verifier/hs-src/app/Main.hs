{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Data.ByteString.Lazy as BSL
import LeiosEvents
import Lib
import Options.Applicative

main :: IO ()
main =
  do
    Command{..} <- execParser commandParser
    BSL.readFile logFile >>= print . verifyTrace . decodeJSONL

newtype Command = Command
  { logFile :: FilePath
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
      <$> strOption
        ( long "trace-file"
            <> help "Short Leios simulation trace log file"
        )
