{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Streaming trace verification of Linear Leios against a running node. The
--   SUT's leadership schedule and the on-chain stake distribution are sourced
--   from the node via the cardano-api; the trace itself is read incrementally
--   from stdin as the node's own tracing log (node.log), parsed natively into
--   Leios 'ChainEvent's (keyed by EB hash). The SUT is the pool given by
--   --stake-pool-id and is the sole node the log describes, so no relabelling
--   is needed.
module Main where

import ChainEvents (ChainEvent (..), parseNodeLog)
import Control.Monad (when)
import Data.ByteString.Lazy as BSL
import Data.Yaml (FromJSON, decodeEither')
import LeadershipSchedule (setLeadershipSchedule)
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
import qualified Data.Text as T (Text, drop, dropWhile, isInfixOf, pack, takeWhile, unpack)

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
      <> " winning slots "
      <> show cdWinningSlots
      <> ", "
      <> show cdNumParties
      <> " parties, SUT at index "
      <> show cdSutIndex
  setLeadershipSchedule cdWinningSlots

  let verify evs =
        verifyChainTraceFromSlot cdNumParties cdSutIndex cdStakeDistribution
          lhdr lvote ldiff validityCheckTime evs startingSlot
  runStreaming verify

-- | Consume the node.log lazily from stdin, parse it into Leios 'ChainEvent's,
--   and re-verify the accumulated prefix at every slot boundary (each
--   'CSlot'), stopping at the first prefix the formal spec rejects.
runStreaming :: ([ChainEvent] -> ([T.Text], (T.Text, T.Text))) -> IO ()
runStreaming verify =
  do
    hSetBuffering stdout LineBuffering
    evs <- parseNodeLog <$> BSL.getContents
    -- A fresh node.log begins with a long sync/replay phase whose Leios events
    -- (vote/block acquisitions for the chain history) precede the node's first
    -- leadership-check slot. They are not part of live per-slot behaviour, so
    -- skip everything up to the first slot tick rather than flooding output.
    let (preSlot, rest) = Prelude.break isCSlot evs
    hPutStrLn stderr $
      "skipped "
        <> show (Prelude.length preSlot)
        <> " pre-slot events (node sync/replay backlog, before the first leadership-check slot)"
    case rest of
      [] -> hPutStrLn stderr "no leadership-check slot found in input — nothing to verify"
      (CSlot s : _) -> hPutStrLn stderr $ "verifying from first leadership-check slot " <> show s
      (ev : _) -> hPutStrLn stderr $ "verifying from " <> show ev
    go [] rest
 where
  go :: [ChainEvent] -> [ChainEvent] -> IO ()
  go seen [] = finish (Prelude.reverse seen)
  go seen (ev : rest) =
    do
      hPutStrLn stderr $ "event: " <> show ev
      if isCSlot ev
        then checkpoint (Prelude.reverse seen') >> go seen' rest
        else go seen' rest
   where
    seen' = ev : seen
  checkpoint prefix =
    let (acts, (status, detail)) = verify prefix
     in if status == "ok"
          then
            hPutStrLn stderr $
              "ok @ " <> show (Prelude.length prefix) <> " events, " <> show (Prelude.length acts) <> " actions"
          else failOut prefix acts status detail
  finish prefix =
    let (acts, (status, detail)) = verify prefix
     in if status == "ok"
          then hPutStrLn stderr "stream ended: ok" >> printActions acts
          else failOut prefix acts status detail
  printActions = mapM_ (\a -> hPutStrLn stderr ("  action: " <> T.unpack a))
  -- The slot an action or error status belongs to: the leading token of the
  -- status ("<slot> : Err-…"), or the token after the first '@' of an action
  -- ("VT-Role@<slot> …").
  slotOfAction a = T.takeWhile (/= ' ') (T.drop 1 (T.dropWhile (/= '@') a))
  failOut prefix acts status detail =
    do
      hPutStrLn stderr $
        "VIOLATION after " <> show (Prelude.length prefix) <> " events: " <> T.unpack status
      hPutStrLn stderr $ T.unpack detail
      -- Err-Invalid is the spec's generic catch-all with no detail; explain it.
      when ("Err-Invalid" `T.isInfixOf` status) $
        hPutStrLn stderr $
          "  (Err-Invalid: a No-EB-Role/No-VT-Role abstention was rejected — the spec "
            <> "permits abstaining only when the role cannot be performed this slot. "
            <> "Under the exact-offset spec a vote is mandated at slotNumber(eb) + "
            <> "validityCheckTime; the vote-window spec relaxes this.)"
      -- Only the actions in the failing slot.
      let failSlot = T.takeWhile (/= ' ') status
      printActions (Prelude.filter ((== failSlot) . slotOfAction) acts)
      exitFailure

-- | True iff the event is a slot tick (used as a re-verification checkpoint).
isCSlot :: ChainEvent -> Bool
isCSlot (CSlot _) = True
isCSlot _ = False

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
   in ChainData
        { cdWinningSlots = winning
        , cdNumParties = toInteger (Prelude.length pairs)
        , cdStakeDistribution = stakeDist
        , cdSutIndex = sutIdx
        }

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
