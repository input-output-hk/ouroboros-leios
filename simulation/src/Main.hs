{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Control.Applicative (Alternative ((<|>)), optional)
import Data.Maybe (fromMaybe)
import qualified Options.Applicative as Opts

import Viz (
  AnimVizConfig (..),
  GtkVizConfig (..),
  defaultAnimVizConfig,
  defaultGtkVizConfig,
  vizualise,
  writeAnimationFrames,
 )
import VizName (VizName (..), namedViz)

main :: IO ()
main = do
  cmd <- Opts.execParser cli
  case cmd of
    Run opts ->
      runViz opts
    List -> listVisualizations

runViz :: RunOptions -> IO ()
runViz RunOptions{cliVizName, cliOutputFramesDir, cliOutputSeconds, cliOutputStartTime, cliCpuRendering, cliVizSize} = do
  let viz = namedViz cliVizName
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

listVisualizations :: IO ()
listVisualizations = do
  putStrLn "Available visualisations:"
  mapM_ (putStrLn . ("  " ++) . show) $ enumFrom VizTCP1

cli :: Opts.ParserInfo Command
cli =
  Opts.info
    (Opts.helper <*> command)
    ( Opts.fullDesc
        <> Opts.header "Vizualisations of Ouroboros-related network simulations"
        <> Opts.progDesc
          "Either show a visualisation in a window, or output \
          \ animation frames to a directory."
    )

data RunOptions = RunOptions
  { cliVizName :: VizName
  , cliOutputFramesDir :: Maybe FilePath
  , cliOutputSeconds :: Maybe Int
  , cliOutputStartTime :: Maybe Int
  , cliCpuRendering :: Bool
  , cliVizSize :: Maybe (Int, Int)
  }

data Command = Run RunOptions | List

command :: Opts.Parser Command
command =
  Opts.hsubparser
    ( Opts.command "run" (Opts.info (Run <$> options) (Opts.progDesc "Run a visualisation"))
        <> Opts.command "list" (Opts.info (pure List) (Opts.progDesc "List available visualisations"))
    )

options :: Opts.Parser RunOptions
options =
  RunOptions
    <$> Opts.argument
      Opts.auto
      (Opts.metavar "VIZNAME")
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
