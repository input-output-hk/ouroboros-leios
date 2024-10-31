{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Control.Applicative (optional)
import Data.Maybe (fromMaybe)
import Data.String (IsString (fromString))
import qualified Options.Applicative as Opts
import Options.Applicative.Help (line)
import qualified PraosProtocol.ExamplesPraosP2P as VizPraosP2P
import System.FilePath
import TimeCompat

main :: IO ()
main = do
  CliCmd
    { cliSim = (name, (defaultS, sim))
    , cliOutputSeconds
    , cliOutputFile
    } <-
    Opts.execParser cli
  let seconds = fromMaybe defaultS $ Time . fromIntegral <$> cliOutputSeconds
  let filename = fromMaybe (name <.> "json") $ cliOutputFile
  sim seconds filename

cli :: Opts.ParserInfo CliCmd
cli =
  Opts.info
    (Opts.helper <*> options)
    ( Opts.fullDesc
        <> Opts.header "Sampling of Ouroboros-related network simulations"
        <> Opts.progDescDoc (Just desc)
    )
 where
  desc =
    fromString
      "Gather data from a simulation."
      <> line
      <> fromString vizNamesHelp

type Sim = (Time, Time -> FilePath -> IO ())
data CliCmd = CliCmd
  { cliSim :: (String, Sim)
  , cliOutputSeconds :: Maybe Int
  , cliOutputFile :: Maybe FilePath
  }

vizNamesHelp :: String
vizNamesHelp = "SIMNAME is one of: " ++ unwords (map fst simulations)

options :: Opts.Parser CliCmd
options =
  CliCmd
    <$> Opts.argument
      (Opts.eitherReader readViz)
      ( Opts.metavar "SIMNAME"
          <> Opts.help vizNamesHelp
      )
    <*> optional
      ( Opts.option
          Opts.auto
          ( Opts.long "seconds"
              <> Opts.metavar "SEC"
              <> Opts.help "Run N seconds of simulated time."
          )
      )
    <*> optional
      ( Opts.option
          Opts.auto
          ( Opts.long "output"
              <> Opts.metavar "FILENAME"
              <> Opts.help "output filename, (default SIMNAME.json)"
          )
      )

simulations :: [(String, Sim)]
simulations =
  [ ("praos-diffusion-10-links", (Time 40, VizPraosP2P.example1000Diffusion 5 5))
  , ("praos-diffusion-20-links", (Time 40, VizPraosP2P.example1000Diffusion 10 10))
  ]

readViz :: String -> Either String (String, Sim)
readViz s = case lookup s simulations of
  Just viz -> Right (s, viz)
  Nothing -> Left "unknown sim"
