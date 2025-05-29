{-# LANGUAGE RecordWildCards #-}

module Main (
  main,
) where

import Control.Applicative ((<**>))
import Leios.Tracing.Processor (process)

import qualified Options.Applicative as O

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    process logFile lifecycleFile

data Command = Command
  { logFile :: FilePath
  , lifecycleFile :: FilePath
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  O.info (com <**> O.helper) $
    O.fullDesc
      <> O.progDesc "Leios trace processor"
      <> O.header "Process Leios trace logs into CSV file abstracts"
 where
  com =
    Command
      <$> O.strOption (O.long "trace-file" <> O.metavar "FILE" <> O.value "/dev/stdin" <> O.help "Input Leios simulation trace log file")
      <*> O.strOption (O.long "lifecycle-file" <> O.metavar "FILE" <> O.help "Output CSV file for transaction lifecycle data")
