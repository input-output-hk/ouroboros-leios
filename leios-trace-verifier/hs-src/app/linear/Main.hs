{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Main entry for trace verification of Linear Leios.
module Main where

import Control.Monad (unless)
import Data.ByteString.Lazy as BSL
import Data.Map
import Data.Yaml (FromJSON, decodeEither', decodeFileThrow)
import LeadershipSchedule (setLeadershipSchedule)
import LeiosConfig (Config (..))
import LeiosEvents
import LeiosTopology (LocationKind (..), Node (..), NodeInfo (..), NodeName (..), Topology (..))
import LinearLeiosLib
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (BufferMode (LineBuffering), hPutStrLn, hSetBuffering, stderr, stdout)

import qualified Cardano.Api as Api
import qualified Data.ByteString as BS (ByteString, readFile)
import qualified Data.ByteString.Char8 as BSC (pack)
import qualified Data.Set as Set
import qualified Data.Text as T (Text, pack, unpack)

-- | Run the CLI.
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

    -- Install the SUT's leadership schedule (winning slots) into the oracle
    -- postulated by the Agda spec. When --socket-path is given we query a
    -- running node through the cardano-api; otherwise the schedule stays empty
    -- and the verifier falls back to harvesting winning slots from the trace.
    case leadership of
      Nothing -> pure ()
      Just opts -> do
        slots <- queryLeadershipSchedule opts
        hPutStrLn stderr $ "Leadership schedule: " <> show (Prelude.length slots) <> " winning slots"
        setLeadershipSchedule slots

    -- A single closure capturing all parameters: it applies the (whole-list)
    -- Agda checker to a list of events, returning (#actions, (status, detail)).
    let verify evs =
          verifyTraceFromSlot nrNodes idSut stakeDistribution
            lhdr lvote ldiff validityCheckTime evs startingSlot

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
--   'message' is not a field selector ('NoFieldSelectors' in 'LeiosEvents'),
--   so we match it via record-pattern syntax.
isSlot :: TraceEvent -> Bool
isSlot TraceEvent{message = m} = case m of
  Slot{} -> True
  _ -> False

-- * Leadership schedule via cardano-api

-- | Which epoch's leadership schedule to query.
data WhichEpoch = CurrentEpoch | NextEpoch
  deriving (Eq, Ord, Read, Show)

-- | Connection / key parameters needed to query a node's leadership schedule.
--   Mirrors @cardano-cli query leadership-schedule@.
data LeadershipOpts = LeadershipOpts
  { loSocketPath :: FilePath
  , loNetworkId :: Api.NetworkId
  , loGenesisFile :: FilePath
  , loStakePoolId :: Api.PoolId
  , loVrfSkeyFile :: FilePath
  , loWhich :: WhichEpoch
  }

-- | Query a running node (via the cardano-api local-state-query protocol) for
--   the slots in which the given pool is an eligible leader, returning them as
--   plain naturals for the Agda oracle. Mirrors cardano-cli's
--   @runQueryLeadershipScheduleCmd@.
queryLeadershipSchedule :: LeadershipOpts -> IO [Integer]
queryLeadershipSchedule LeadershipOpts{..} = do
  vrfSkey <-
    Api.readFileTextEnvelope @(Api.SigningKey Api.VrfKey) (Api.File loVrfSkeyFile)
      >>= orDie "reading VRF signing key"
  (shelleyGenesis :: Api.ShelleyGenesis) <-
    BS.readFile loGenesisFile
      >>= orDie "decoding Shelley genesis" . eitherDecodeStrictText
  let connInfo =
        Api.LocalNodeConnectInfo
          { Api.localConsensusModeParams = Api.CardanoModeParams (Api.EpochSlots 21600)
          , Api.localNodeNetworkId = loNetworkId
          , Api.localNodeSocketPath = Api.File loSocketPath
          }
  (result :: Either Api.AcquiringFailure (Either Api.LeadershipError (Set.Set Api.SlotNo))) <-
    Api.executeLocalStateQueryExpr connInfo Api.VolatileTip $ do
      Api.AnyCardanoEra era <- expectQuery "current era" Api.queryCurrentEra
      Api.caseByronOrShelleyBasedEra
        (error "Byron era is not supported")
        ( \sbe -> do
            pparams <- expectQueryEra "protocol parameters" (Api.queryProtocolParameters sbe)
            ptclState <- expectQueryEra "protocol state" (Api.queryProtocolState sbe)
            eraHistory <- expectQuery "era history" Api.queryEraHistory
            let eInfo = Api.unLedgerEpochInfo (Api.toLedgerEpochInfo eraHistory)
            currentEpoch <- expectQueryEra "epoch" (Api.queryEpoch sbe)
            beo <- case Api.forEraMaybeEon (Api.toCardanoEra sbe) of
              Just b -> pure b
              Nothing -> error "Era does not support the pool distribution query"
            serPoolDistr <-
              expectQueryEra "pool distribution"
                (Api.queryPoolDistribution beo (Just (Set.singleton loStakePoolId)))
            pure $
              case loWhich of
                CurrentEpoch ->
                  Api.currentEpochEligibleLeadershipSlots
                    sbe shelleyGenesis eInfo pparams ptclState loStakePoolId vrfSkey serPoolDistr currentEpoch
                NextEpoch ->
                  error "next-epoch schedule not yet implemented"
        )
        era
  case result of
    Left err -> die ("local state query failed: " <> show err)
    Right (Left lerr) -> die ("leadership schedule error: " <> show lerr)
    Right (Right slots) -> pure (Prelude.map (toInteger . Api.unSlotNo) (Set.toList slots))

-- | Run a non-era-mismatch query, dying on an unsupported node-to-client version.
expectQuery ::
  Show e =>
  String ->
  Api.LocalStateQueryExpr block point Api.QueryInMode r IO (Either e a) ->
  Api.LocalStateQueryExpr block point Api.QueryInMode r IO a
expectQuery what q =
  q >>= \case
    Left e -> error (what <> ": " <> show e)
    Right a -> pure a

-- | Run a query that can additionally fail with an era mismatch.
expectQueryEra ::
  (Show e1, Show e2) =>
  String ->
  Api.LocalStateQueryExpr block point Api.QueryInMode r IO (Either e1 (Either e2 a)) ->
  Api.LocalStateQueryExpr block point Api.QueryInMode r IO a
expectQueryEra what q =
  q >>= \case
    Left e -> error (what <> ": " <> show e)
    Right (Left e) -> error (what <> " (era mismatch): " <> show e)
    Right (Right a) -> pure a

orDie :: Show e => String -> Either e a -> IO a
orDie what = either (\e -> die (what <> ": " <> show e)) pure

die :: String -> IO a
die msg = hPutStrLn stderr msg >> exitFailure

-- | Decode strict JSON/YAML bytes (the Shelley genesis) via aeson/yaml.
eitherDecodeStrictText :: FromJSON a => BS.ByteString -> Either String a
eitherDecodeStrictText = either (Left . show) Right . decodeEither'

-- | CLI commands.
data Command = Command
  { logFile :: FilePath
  , configFile :: FilePath
  , topologyFile :: FilePath
  , startingSlot :: Integer
  , idSut :: Integer
  , streaming :: Bool
  , leadership :: Maybe LeadershipOpts
  }

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
      <*> optional leadershipParser

-- | Parser for the cardano-api leadership-schedule query options. Presence of
--   --socket-path enables querying a node for the SUT's winning slots.
leadershipParser :: Parser LeadershipOpts
leadershipParser =
  LeadershipOpts
    <$> strOption (long "socket-path" <> metavar "FILE" <> help "Node socket for the cardano-api leadership-schedule query")
    <*> networkIdParser
    <*> strOption (long "shelley-genesis" <> metavar "FILE" <> help "Shelley genesis file")
    <*> option (eitherReader readPoolId) (long "stake-pool-id" <> metavar "POOLID" <> help "Stake pool id (bech32 or hex)")
    <*> strOption (long "vrf-signing-key-file" <> metavar "FILE" <> help "VRF signing key file")
    <*> flag CurrentEpoch NextEpoch (long "next" <> help "Query the next epoch's schedule (default: current)")

networkIdParser :: Parser Api.NetworkId
networkIdParser =
  flag' Api.Mainnet (long "mainnet" <> help "Use the mainnet magic id")
    <|> ( Api.Testnet . Api.NetworkMagic
            <$> option auto (long "testnet-magic" <> metavar "NATURAL" <> help "Testnet network magic")
        )

readPoolId :: String -> Either String Api.PoolId
readPoolId s =
  case Api.deserialiseFromBech32 (T.pack s) of
    Right (p :: Api.PoolId) -> Right p
    Left _ ->
      case Api.deserialiseFromRawBytesHex (BSC.pack s) of
        Right (p :: Api.PoolId) -> Right p
        Left e -> Left ("invalid stake pool id: " <> show e)
