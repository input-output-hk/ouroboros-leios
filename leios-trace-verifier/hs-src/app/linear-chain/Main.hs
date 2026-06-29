{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
-- The record-wildcard relabelling below binds fields such as 'id', which would
-- otherwise shadow Prelude names.
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Streaming trace verification of Linear Leios that sources the SUT's
--   leadership schedule and the stake distribution from a running node via the
--   cardano-api. The trace is read incrementally from stdin; the SUT is the
--   pool given by --stake-pool-id and trace producers (pool-ids) are relabelled
--   to the verifier's @node-i@ party identities.
module Main where

import Data.ByteString.Lazy as BSL
import Data.Yaml (FromJSON, decodeEither')
import LeadershipSchedule (setLeadershipSchedule)
import LeiosEvents
import LinearLeiosLib
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (BufferMode (LineBuffering), hPutStrLn, hSetBuffering, stderr, stdout)

import qualified Cardano.Api as Api
import qualified Data.ByteString as BS (ByteString, readFile)
import qualified Data.ByteString.Char8 as BSC (pack)
import qualified Data.List as List (findIndex)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T (Text, pack, unpack)

-- | Run the CLI: query the chain, then stream-verify the trace from stdin.
main :: IO ()
main = do
  ChainCommand{..} <- execParser commandParser

  let lhdr = 1
  let lvote = 4
  let ldiff = 7
  let validityCheckTime = 3

  ChainData{..} <- queryChain leadershipOpts
  hPutStrLn stderr $
    "From chain: "
      <> show (Prelude.length cdWinningSlots)
      <> " winning slots, "
      <> show cdNumParties
      <> " parties, SUT at index "
      <> show cdSutIndex
  setLeadershipSchedule cdWinningSlots

  let relabel = relabelTraceEvent (\t -> Map.findWithDefault t t cdRelabel)
      verify evs =
        verifyTraceFromSlot cdNumParties cdSutIndex cdStakeDistribution
          lhdr lvote ldiff validityCheckTime evs startingSlot
  runStreaming relabel verify

-- | Consume JSONL trace events lazily from stdin, relabel pool-ids to @node-i@,
--   and re-verify the accumulated prefix at every slot boundary, stopping at
--   the first prefix the formal spec rejects.
runStreaming :: (TraceEvent -> TraceEvent) -> ([TraceEvent] -> (Integer, (T.Text, T.Text))) -> IO ()
runStreaming relabel verify =
  do
    hSetBuffering stdout LineBuffering
    evs <- Prelude.map relabel . decodeJSONL <$> BSL.getContents
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

-- * Reading from the chain via cardano-api

-- | Which epoch's leadership schedule to query.
data WhichEpoch = CurrentEpoch | NextEpoch
  deriving (Eq, Ord, Read, Show)

-- | Connection / key parameters for the node queries. Mirrors
--   @cardano-cli query leadership-schedule@.
data LeadershipOpts = LeadershipOpts
  { loSocketPath :: FilePath
  , loNetworkId :: Api.NetworkId
  , loGenesisFile :: FilePath
  , loStakePoolId :: Api.PoolId
  , loVrfSkeyFile :: FilePath
  , loWhich :: WhichEpoch
  }

-- | Everything we read from the chain for verification.
data ChainData = ChainData
  { cdWinningSlots :: [Integer]
  -- ^ The SUT's leadership schedule, as plain naturals for the Agda oracle.
  , cdNumParties :: Integer
  -- ^ Number of parties (= number of stake pools).
  , cdStakeDistribution :: [(T.Text, Integer)]
  -- ^ Per-party stake, keyed @node-i@ (pool i in chain order).
  , cdSutIndex :: Integer
  -- ^ The SUT's party index (position of --stake-pool-id in chain order).
  , cdRelabel :: Map.Map T.Text T.Text
  -- ^ Maps each pool-id (bech32 and hex forms) to its @node-i@ identity, so
  --   trace producers can be relabelled to what the verifier expects.
  }

-- | Query a running node (via the cardano-api local-state-query protocol) for
--   the SUT's leadership schedule (the slots in which its pool is an eligible
--   leader) and the on-chain stake distribution, over a single connection.
--   Mirrors cardano-cli's @runQueryLeadershipScheduleCmd@ /
--   @runQueryStakeDistributionCmd@.
queryChain :: LeadershipOpts -> IO ChainData
queryChain LeadershipOpts{..} = do
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
  ( result ::
      Either
        Api.AcquiringFailure
        ( Either Api.LeadershipError (Set.Set Api.SlotNo)
        , Map.Map (Api.Hash Api.StakePoolKey) Rational
        )
    ) <-
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
            stakeDistr <- expectQueryEra "stake distribution" (Api.queryStakeDistribution sbe)
            let schedule =
                  case loWhich of
                    CurrentEpoch ->
                      Api.currentEpochEligibleLeadershipSlots
                        sbe shelleyGenesis eInfo pparams ptclState loStakePoolId vrfSkey serPoolDistr currentEpoch
                    NextEpoch ->
                      error "next-epoch schedule not yet implemented"
            pure (schedule, stakeDistr)
        )
        era
  case result of
    Left err -> die ("local state query failed: " <> show err)
    Right (Left lerr, _) -> die ("leadership schedule error: " <> show lerr)
    Right (Right slots, stakeDistr) ->
      pure $ buildChainData loStakePoolId (Prelude.map (toInteger . Api.unSlotNo) (Set.toList slots)) stakeDistr

-- | Turn the on-chain stake distribution (pool-id → relative stake) into the
--   verifier's view: parties are the pools in chain (Map) order, keyed
--   @node-i@; the SUT is the pool given by --stake-pool-id, at its natural
--   index. Relative stakes are scaled to naturals (per billion).
buildChainData ::
  Api.PoolId ->
  [Integer] ->
  Map.Map (Api.Hash Api.StakePoolKey) Rational ->
  ChainData
buildChainData sutPool winning m =
  let pairs = Map.toList m -- sorted by pool-id, deterministic
      nodeName i = T.pack ("node-" <> show (i :: Int))
      scaleStake r = floor (r * 1000000000) :: Integer
      stakeDist = [(nodeName i, scaleStake r) | (i, (_, r)) <- Prelude.zip [0 ..] pairs]
      sutIdx =
        maybe (error "SUT stake pool not found in chain stake distribution") toInteger $
          List.findIndex ((== sutPool) . fst) pairs
      relabelMap =
        Map.fromList $
          Prelude.concat
            [ [(Api.serialiseToBech32 pid, nodeName i), (Api.serialiseToRawBytesHexText pid, nodeName i)]
            | (i, (pid, _)) <- Prelude.zip [0 ..] pairs
            ]
   in ChainData
        { cdWinningSlots = winning
        , cdNumParties = toInteger (Prelude.length pairs)
        , cdStakeDistribution = stakeDist
        , cdSutIndex = sutIdx
        , cdRelabel = relabelMap
        }

-- | Rewrite the node-identity fields (producer / node / sender / recipient /
--   publisher) of a trace event through the given relabelling, leaving all
--   other fields untouched. Used to map chain pool-ids to @node-i@ identities.
relabelTraceEvent :: (T.Text -> T.Text) -> TraceEvent -> TraceEvent
relabelTraceEvent f TraceEvent{..} = TraceEvent{message = relabelEvent f message, ..}

relabelEvent :: (T.Text -> T.Text) -> Event -> Event
relabelEvent f = \case
  Slot{..} -> Slot{node = f node, ..}
  Cpu{..} -> Cpu{node = f node, ..}
  NoIBGenerated{..} -> NoIBGenerated{node = f node, ..}
  NoEBGenerated{..} -> NoEBGenerated{node = f node, ..}
  NoVTBundleGenerated{..} -> NoVTBundleGenerated{node = f node, ..}
  IBSent{..} -> IBSent{sender = f <$> sender, recipient = f recipient, ..}
  EBSent{..} -> EBSent{sender = f <$> sender, recipient = f recipient, ..}
  VTBundleSent{..} -> VTBundleSent{sender = f <$> sender, recipient = f recipient, ..}
  RBSent{..} -> RBSent{sender = f <$> sender, recipient = f recipient, ..}
  IBReceived{..} -> IBReceived{sender = f <$> sender, recipient = f recipient, ..}
  EBReceived{..} -> EBReceived{sender = f <$> sender, recipient = f recipient, ..}
  VTBundleReceived{..} -> VTBundleReceived{sender = f <$> sender, recipient = f recipient, ..}
  RBReceived{..} -> RBReceived{sender = f <$> sender, recipient = f recipient, ..}
  TXReceived{..} -> TXReceived{sender = f <$> sender, recipient = f recipient, ..}
  IBEnteredState{..} -> IBEnteredState{node = f node, ..}
  EBEnteredState{..} -> EBEnteredState{node = f node, ..}
  VTBundleEnteredState{..} -> VTBundleEnteredState{node = f node, ..}
  RBEnteredState{..} -> RBEnteredState{node = f node, ..}
  IBGenerated{..} -> IBGenerated{producer = f producer, ..}
  EBGenerated{..} -> EBGenerated{producer = f producer, ..}
  RBGenerated{..} -> RBGenerated{producer = f producer, ..}
  VTBundleGenerated{..} -> VTBundleGenerated{producer = f producer, ..}
  TXGenerated{..} -> TXGenerated{publisher = f publisher, ..}

expectQuery ::
  Show e =>
  String ->
  Api.LocalStateQueryExpr block point Api.QueryInMode r IO (Either e a) ->
  Api.LocalStateQueryExpr block point Api.QueryInMode r IO a
expectQuery what q =
  q >>= \case
    Left e -> error (what <> ": " <> show e)
    Right a -> pure a

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

-- | CLI command.
data ChainCommand = ChainCommand
  { startingSlot :: Integer
  , leadershipOpts :: LeadershipOpts
  }

commandParser :: ParserInfo ChainCommand
commandParser =
  info (com <**> helper) $
    fullDesc
      <> progDesc "Linear Leios streaming trace verifier (reads schedule and stake distribution from a node via cardano-api)"
      <> header "Leios trace verifier (chain)"
 where
  com =
    ChainCommand
      <$> option auto (long "starting-slot" <> value 0 <> help "Starting slot of the trace")
      <*> leadershipParser

-- | Parser for the cardano-api node-query options.
leadershipParser :: Parser LeadershipOpts
leadershipParser =
  LeadershipOpts
    <$> strOption (long "socket-path" <> metavar "FILE" <> help "Node socket for the cardano-api queries")
    <*> networkIdParser
    <*> strOption (long "shelley-genesis" <> metavar "FILE" <> help "Shelley genesis file")
    <*> option (eitherReader readPoolId) (long "stake-pool-id" <> metavar "POOLID" <> help "SUT's stake pool id (bech32 or hex)")
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
