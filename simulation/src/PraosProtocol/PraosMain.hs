{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Functor law" #-}

module Main where

import Data.Functor ((<&>))
import Data.Maybe (fromMaybe)
import qualified Options.Applicative as Opts
import Topology

main :: IO ()
main = do
  CliCmd{..} <- Opts.execParser cli
  networkGraph <-
    readTopology cliTopologyFile
      <&> fromMaybe (error $ "praos: could not parse network topology " <> cliTopologyFile)
      <&> toGraphWithPositionInformation
  print networkGraph

newtype CliCmd = CliCmd
  { cliTopologyFile :: FilePath
  }

cli :: Opts.ParserInfo CliCmd
cli =
  Opts.info
    (Opts.helper <*> options)
    ( Opts.fullDesc
        <> Opts.header "Vizualisations of Praos protocol simulations"
    )

options :: Opts.Parser CliCmd
options =
  CliCmd
    <$> Opts.strArgument
      ( Opts.metavar "FILENAME"
          <> Opts.help "A network topology file."
      )
