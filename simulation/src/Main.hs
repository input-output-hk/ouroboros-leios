{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Control.Applicative (Alternative ((<|>)), optional)
import Data.Maybe (fromMaybe)
import Data.String (IsString (fromString))
import qualified ExamplesRelay
import qualified ExamplesRelayP2P
import qualified ExamplesTCP
import qualified LeiosProtocol.VizSimTestRelay as VizSimTestRelay
import qualified Options.Applicative as Opts
import Options.Applicative.Help (line)
import qualified PraosProtocol.ExamplesPraosP2P as VizPraosP2P
import qualified PraosProtocol.VizSimBlockFetch as VizBlockFetch
import qualified PraosProtocol.VizSimChainSync as VizChainSync
import qualified PraosProtocol.VizSimPraos as VizPraos
import Viz

main :: IO ()
main = do
  CliCmd
    { cliViz = viz
    , cliOutputFramesDir
    , cliOutputSeconds
    , cliOutputStartTime
    , cliCpuRendering
    , cliVizSize
    } <-
    Opts.execParser cli
  case cliOutputFramesDir of
    Nothing ->
      vizualise config viz
     where
      config =
        defaultGtkVizConfig
          { gtkVizCpuRendering = cliCpuRendering
          , gtkVizResolution = cliVizSize
          }
    Just outdir ->
      writeAnimationFrames config viz
     where
      config =
        defaultAnimVizConfig
          { animVizFrameFiles = \n -> outdir ++ "/frame-" ++ show n ++ ".png"
          , animVizDuration = fromMaybe 60 cliOutputSeconds
          , animVizStartTime = fromMaybe 0 cliOutputStartTime
          , animVizResolution = cliVizSize
          }

cli :: Opts.ParserInfo CliCmd
cli =
  Opts.info
    (Opts.helper <*> options)
    ( Opts.fullDesc
        <> Opts.header "Vizualisations of Ouroboros-related network simulations"
        <> Opts.progDescDoc (Just desc)
    )
 where
  desc =
    fromString
      "Either show a visualisation in a window, or output \
      \ animation frames to a directory."
      <> line
      <> fromString ("VIZNAME is one of: " ++ unwords (map fst vizualisations))

data CliCmd = CliCmd
  { cliViz :: Vizualisation
  , cliOutputFramesDir :: Maybe FilePath
  , cliOutputSeconds :: Maybe Int
  , cliOutputStartTime :: Maybe Int
  , cliCpuRendering :: Bool
  , cliVizSize :: Maybe (Int, Int)
  }

vizNamesHelp :: String
vizNamesHelp = "VIZNAME is one of: " ++ unwords (map fst vizualisations)

options :: Opts.Parser CliCmd
options =
  CliCmd
    <$> Opts.argument
      (Opts.eitherReader readViz)
      ( Opts.metavar "VIZNAME"
          <> Opts.help vizNamesHelp
      )
    <*> optional
      ( Opts.strOption
          ( Opts.long "frames-dir"
              <> Opts.metavar "DIR"
              <> Opts.help "Output animation frames to directory"
          )
      )
    <*> optional
      ( Opts.option
          Opts.auto
          ( Opts.long "seconds"
              <> Opts.metavar "SEC"
              <> Opts.help "Output N seconds of animation"
          )
      )
    <*> optional
      ( Opts.option
          Opts.auto
          ( Opts.long "skip-seconds"
              <> Opts.metavar "SEC"
              <> Opts.help "Skip the first N seconds of animation"
          )
      )
    <*> Opts.switch
      ( Opts.long "cpu-render"
          <> Opts.help "Use CPU-based client side Cairo rendering"
      )
    <*> optional sizeOptions
 where
  sizeOptions :: Opts.Parser (Int, Int)
  sizeOptions =
    Opts.flag'
      (1280, 720)
      ( Opts.long "720p"
          <> Opts.help "Use 720p resolution"
      )
      <|> Opts.flag'
        (1920, 1080)
        ( Opts.long "1080p"
            <> Opts.help "Use 1080p resolution"
        )
      <|> Opts.option
        Opts.auto
        ( Opts.long "resolution"
            <> Opts.metavar "(W,H)"
            <> Opts.help "Use a specific resolution"
        )

vizualisations :: [(String, Vizualisation)]
vizualisations =
  [ ("tcp-1", ExamplesTCP.example1)
  , ("tcp-2", ExamplesTCP.example2)
  , ("tcp-3", ExamplesTCP.example3)
  , ("relay-1", ExamplesRelay.example1)
  , ("relay-2", ExamplesRelay.example2)
  , ("p2p-1", ExamplesRelayP2P.example1)
  , ("p2p-2", ExamplesRelayP2P.example2)
  , ("pcs-1", VizChainSync.example1)
  , ("pbf-1", VizBlockFetch.example1)
  , ("praos-1", VizPraos.example1)
  , ("praos-p2p-1", VizPraosP2P.example1)
  , ("praos-p2p-2", VizPraosP2P.example2)
  , ("relay-test-1", VizSimTestRelay.example1)
  , ("relay-test-2", VizSimTestRelay.example2)
  , ("relay-test-3", VizSimTestRelay.example3)
  ]

readViz :: String -> Either String Vizualisation
readViz s = case lookup s vizualisations of
  Just viz -> Right viz
  Nothing -> Left "unknown vizualisation"
