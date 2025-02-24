module Main where

import Control.Monad (unless)
import Data.Aeson qualified as A
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.List (isPrefixOf, partition)
import Leios.Conformance.ExternalSpec (spec)
import Leios.Conformance.Test.External (NodeRequest (Stop))
import System.Environment (getArgs, withArgs)
import System.Exit (die)
import System.IO (
  BufferMode (LineBuffering),
  IOMode (AppendMode, ReadMode),
  hSetBuffering,
  openFile,
 )
import Test.Hspec (hspec)

main :: IO ()
main = do
  (customArgs, hspecArgs) <- partition (isPrefixOf "--external-") <$> getArgs
  unless (length customArgs == 2) $
    die "Required arguments: --external-input=FILE and --external-output=FILE"
  simin <- case filter (isPrefixOf "--external-input=") customArgs of
    [arg] -> pure $ drop (length "--external-input=") arg
    _ -> die "Missing argument: --external-input=FILE"
  simout <- case filter (isPrefixOf "--external-output=") customArgs of
    [arg] -> pure $ drop (length "--external-output=") arg
    _ -> die "Missing argument: --external-output=FILE"
  hWriter <- openFile simin AppendMode
  hReader <- openFile simout ReadMode
  hSetBuffering hWriter LineBuffering
  hSetBuffering hReader LineBuffering
  withArgs hspecArgs $
    hspec $
      spec hReader hWriter
  LBS8.hPutStrLn hWriter $ A.encode Stop
