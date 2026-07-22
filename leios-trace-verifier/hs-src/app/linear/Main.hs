{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Trace verification of Linear Leios reading all inputs from files (topology,
--   config, and the trace). The SUT's winning slots are harvested from the
--   trace (the leadership-schedule oracle is left empty). For verification that
--   sources the schedule and stake distribution from a running node, use the
--   @linear-leios-trace-verifier-chain@ executable.
module Main where

import Control.Monad (unless)
import Data.ByteString.Lazy as BSL
import Data.Map (elems, keys)
import Data.Yaml (decodeFileThrow)
import LeiosConfig (Config (..))
import LeiosEvents
import LeiosTopology (LocationKind (..), Node (..), NodeInfo (..), NodeName (..), Topology (..))
import LinearLeiosLib
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (BufferMode (LineBuffering), hPutStrLn, hSetBuffering, stderr, stdout)

import qualified Data.Text as T (Text, unpack)

-- | Run the CLI.
main :: IO ()
main =
  do
    Command{..} <- execParser commandParser

    -- Party count and stake distribution from the topology.
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

    -- A single closure capturing all parameters: it applies the (whole-list)
    -- Agda checker to a list of events, returning (#actions, (status, detail)).
    let verify evs =
          verifyTraceFromSlot
            nrNodes
            idSut
            stakeDistribution
            lhdr
            lvote
            ldiff
            validityCheckTime
            evs
            startingSlot

    if streaming
      then runStreaming verify
      else do
        result <- verify . decodeJSONL <$> BSL.readFile logFile
        hPutStrLn stderr $ "Applying " <> show (fst result) <> " actions"
        unless (fst (snd result) == "ok") $
          do
            putStrLn . T.unpack $ fst (snd result)
            putStrLn . T.unpack $ snd (snd result)
            exitFailure

-- | Streaming mode: consume JSONL trace events lazily from stdin and re-verify
--   the accumulated prefix at every slot boundary, stopping at the first prefix
--   that the formal spec rejects.
runStreaming :: ([TraceEvent] -> (Integer, (T.Text, T.Text))) -> IO ()
runStreaming verify =
  do
    hSetBuffering stdout LineBuffering
    evs <- decodeJSONL <$> BSL.getContents
    go [] evs
 where
  go :: [TraceEvent] -> [TraceEvent] -> IO ()
  go seen [] = finish (Prelude.reverse seen)
  go seen (ev : rest)
    | isSlot ev = checkpoint (Prelude.reverse seen') >> go seen' rest
    | otherwise = go seen' rest
   where
    seen' = ev : seen
  checkpoint prefix =
    let (nActs, (status, detail)) = verify prefix
     in if status == "ok"
          then
            hPutStrLn stderr $
              "ok @ " <> show (Prelude.length prefix) <> " events, " <> show nActs <> " actions"
          else failOut prefix status detail
  finish prefix =
    let (_, (status, detail)) = verify prefix
     in if status == "ok"
          then hPutStrLn stderr "stream ended: ok"
          else failOut prefix status detail
  failOut prefix status detail =
    do
      hPutStrLn stderr $
        "VIOLATION after " <> show (Prelude.length prefix) <> " events: " <> T.unpack status
      hPutStrLn stderr $ T.unpack detail
      exitFailure

-- | True iff the event is a slot tick (used as a re-verification checkpoint).
isSlot :: TraceEvent -> Bool
isSlot TraceEvent{message = m} = case m of
  Slot{} -> True
  _ -> False

-- | CLI commands.
data Command = Command
  { logFile :: FilePath
  , configFile :: FilePath
  , topologyFile :: FilePath
  , startingSlot :: Integer
  , idSut :: Integer
  , streaming :: Bool
  }
  deriving (Eq, Ord, Read, Show)

-- | Command parser.
commandParser :: ParserInfo Command
commandParser =
  info (com <**> helper) $
    fullDesc
      <> progDesc "Linear Leios trace verifier"
      <> header "Leios trace verifier"
 where
  com =
    Command
      <$> strOption (long "trace-file" <> value "/dev/stdin" <> help "Leios simulation trace log file (batch mode)")
      <*> strOption (long "config-file" <> help "Leios configuration file")
      <*> strOption (long "topology-file" <> help "Leios topology file")
      <*> option auto (long "starting-slot" <> value 0 <> help "Starting slot of trace-file")
      <*> option auto (long "idSut" <> help "Id of system under test (SUT)")
      <*> switch (long "streaming" <> help "Read JSONL trace events from stdin and verify incrementally")
