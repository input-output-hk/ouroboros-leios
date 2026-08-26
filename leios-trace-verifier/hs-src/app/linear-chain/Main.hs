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

import ChainEvents (parseNodeLog)
import Control.Monad (when)
import Data.ByteString.Lazy as BSL
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Maybe (fromMaybe)
import Data.Yaml (FromJSON (..), decodeEither', withObject, (.:))
import LinearLeiosChain (
  ChainData (..),
  Progress (..),
  Segment (..),
  Timings (..),
  isCSlot,
  runSegmented,
 )
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

-- | Run the CLI: stream-verify the node.log from stdin, re-querying the node's
--   leadership schedule and stake distribution at each epoch boundary.
main :: IO ()
main = do
  ChainCommand{..} <- execParser commandParser

  let timings = Timings{tLhdr = 1, tLvote = 4, tLdiff = 7, tValidityCheckTime = 3}

  hSetBuffering stdout LineBuffering
  evs <- parseNodeLog <$> BSL.getContents
  -- A fresh node.log begins with a long sync/replay phase whose Leios events
  -- (vote/block acquisitions for the chain history) precede the node's first
  -- leadership-check slot; skip them rather than flooding output.
  let (preSlot, rest) = Prelude.break isCSlot evs
  hPutStrLn stderr $
    "skipped "
      <> show (Prelude.length preSlot)
      <> " pre-slot events (node sync/replay backlog, before the first leadership-check slot)"
  -- The schedule explanation is the same every segment, and a run with frequent
  -- slot gaps starts many, so say it in full once and abbreviate after that.
  explained <- newIORef False
  runSegmented render timings (const (queryChain explained leadershipOpts)) rest

-- * Rendering

-- | Render the driver's progress, and abort on a violation. Kept out of
--   "LinearLeiosChain" so the driver stays testable with a collecting reporter.
render :: Progress -> IO ()
render = \case
  Saw ev -> hPutStrLn stderr $ "event: " <> show ev
  SegmentStarted seg spans -> reportSchedule seg spans
  Verified nEvents nActions ->
    hPutStrLn stderr $
      "ok @ " <> show nEvents <> " events, " <> show nActions <> " actions"
  Violation nEvents acts status detail -> failOut nEvents acts status detail
  NothingToVerify ->
    hPutStrLn stderr "no leadership-check slot found in input — nothing to verify"
  StreamEnded acts -> do
    -- The slot in progress when the input ended is deliberately not adjudicated: a
    -- stream truncated mid-slot has not yet shown the events that would discharge
    -- that slot's obligations.
    hPutStrLn stderr "stream ended: ok (slot in progress at end of input left unverified)"
    printActions acts
  LeiosInactive led ->
    hPutStrLn stderr $
      "warning: the log shows no Leios activity — no EB forged, acquired, announced "
        <> "or voted — so EB-role enforcement is suppressed for the "
        <> show led
        <> " slot(s) the node led, and at least one of those had a mempool too large "
        <> "for its ranking block, so an EB was owed there. NodeIsLeader alone is "
        <> "Praos leadership, and only implies EB eligibility while Leios is actually "
        <> "running — but a node with an oversized mempool doing nothing Leios-side "
        <> "at all is worth looking into."
  SlotGap from to ->
    hPutStrLn stderr $
      "note: no leadership check logged for slot(s) "
        <> show (from + 1)
        <> ".."
        <> show (to - 1)
        <> " — verification restarts at "
        <> show to
        <> ". The spec advances one slot at a time, so a slot with no record cannot "
        <> "be verified across; obligations straddling the gap are not checked."
  EBOwedUndecided n ->
    hPutStrLn stderr $
      "note: for "
        <> show n
        <> " slot(s) the mempool reading straddled the ranking block's capacity, so "
        <> "whether an EB was owed could not be settled; those slots were excused. "
        <> "The node decides from a snapshot the log does not pin down, so this is "
        <> "the cost of never flagging a slot we cannot show was in breach."
  NoMempoolReadings ->
    hPutStrLn stderr $
      "warning: no mempool readings in this prefix, so EB-role enforcement lapses "
        <> "for slots without a forge — an EB can only be shown to be owed when the "
        <> "mempool is known not to have fitted in the ranking block. Expected for "
        <> "logs predating the Mempool traces."
  Summary entries -> summarize entries

reportSchedule :: Segment -> Bool -> IO ()
reportSchedule seg spansEpochs = do
  hPutStrLn stderr $
    "epoch "
      <> show ep
      <> " (from slot "
      <> show (segStart seg)
      <> (if spansEpochs then ", carrying the tail of the previous epoch" else "")
      <> "): "
      <> show (cdNumParties cd)
      <> " parties, SUT at index "
      <> show (cdSutIndex cd)
      <> ", eligibility from "
      <> source
  when (segAuthoritative seg) (warnSlotsOutsideEpoch cd ep)
 where
  cd = segCD seg
  ep = segEpoch seg
  source = case cdWinningSlots cd of
    Nothing -> "the log (the node could supply no schedule)"
    Just slots
      | segAuthoritative seg ->
          "the node schedule: "
            <> show (Prelude.length slots)
            <> " winning slots "
            <> show slots
      | spansEpochs ->
          "the log (this segment spans two epochs, so the schedule "
            <> show slots
            <> " for epoch "
            <> show (cdNodeEpoch cd)
            <> " cannot govern all of it)"
      | otherwise ->
          "the log (the node answered for epoch "
            <> show (cdNodeEpoch cd)
            <> ", so its schedule "
            <> show slots
            <> " does not apply here)"

-- The node claims this epoch, so its winning slots ought to lie inside it. If any do
-- not, an assumption is wrong — epochLength, or which epoch the schedule is computed
-- for — and this segment is being verified unsoundly. Report loudly rather than
-- refuse: refusing has already proved too blunt, and this is precisely the diagnostic
-- needed to tell which assumption is off.
warnSlotsOutsideEpoch :: ChainData -> Integer -> IO ()
warnSlotsOutsideEpoch cd ep =
  case Prelude.filter (not . inEpoch) (fromMaybe [] (cdWinningSlots cd)) of
    [] -> pure ()
    out ->
      hPutStrLn stderr $
        "warning: node reported epoch "
          <> show ep
          <> " but winning slots "
          <> show out
          <> " fall outside its slot range "
          <> show (ep * len)
          <> ".."
          <> show ((ep + 1) * len - 1)
          <> " (they lie in epoch(s) "
          <> show (Prelude.map (`div` len) out)
          <> "); verification of this segment is unsound"
 where
  len = cdEpochLength cd
  inEpoch sl = sl >= ep * len && sl < (ep + 1) * len

-- Every segment is verified, so the interesting distinction is which eligibility
-- source each epoch used. A log-derived one is the SUT's self-report, so it cannot
-- catch the node's own leadership logging being wrong; it is worth knowing where the
-- guarantee is weaker.
summarize :: [(Integer, Bool)] -> IO ()
summarize entries
  | Prelude.null entries = hPutStrLn stderr "summary: no segment was verified"
  | otherwise =
      hPutStrLn stderr $
        "summary: verified epoch(s) "
          <> show (Prelude.map fst entries)
          <> "; eligibility from the node schedule for "
          <> (if Prelude.null fromSchedule then "none" else show fromSchedule)
          <> ", from the log for "
          <> (if Prelude.null fromLog then "none" else show fromLog)
 where
  fromSchedule = [ep | (ep, True) <- entries]
  fromLog = [ep | (ep, False) <- entries]

printActions :: [T.Text] -> IO ()
printActions = mapM_ (\a -> hPutStrLn stderr ("  action: " <> T.unpack a))

-- | The slot an action or error status belongs to.
slotOfAction :: T.Text -> T.Text
slotOfAction a = T.takeWhile (/= ' ') (T.drop 1 (T.dropWhile (/= '@') a))

failOut :: Int -> [T.Text] -> T.Text -> T.Text -> IO ()
failOut nEvents acts status detail = do
  hPutStrLn stderr $
    "VIOLATION after " <> show nEvents <> " events: " <> T.unpack status
  hPutStrLn stderr $ T.unpack detail
  when ("Err-Invalid" `T.isInfixOf` status) $
    hPutStrLn stderr $
      "  (Err-Invalid: a No-EB-Role/No-VT-Role abstention was rejected — the spec "
        <> "permits abstaining only when the role cannot be performed this slot.)"
  -- Only the actions in the failing slot.
  let failSlot = T.takeWhile (/= ' ') status
  printActions (Prelude.filter ((== failSlot) . slotOfAction) acts)
  exitFailure

-- * Reading from the chain via cardano-api

-- | Minimal view of the Shelley genesis: the epoch length (slots/epoch) and the
--   ranking block's body capacity.
--
--   'maxBlockBodySize' is taken from genesis rather than from the protocol-params
--   query, so it is the network's initial value; an on-chain parameter update would
--   leave it stale. Acceptable for now because it is used only to decide whether the
--   mempool could have fitted in an RB, and the comparison is deliberately one-sided,
--   but it is the value to source from 'pparams' if that ever matters.
data GenesisEL = GenesisEL Integer Integer

instance FromJSON GenesisEL where
  parseJSON = withObject "ShelleyGenesis" $ \o -> do
    el <- o .: "epochLength"
    pp <- o .: "protocolParams"
    mb <- pp .: "maxBlockBodySize"
    pure (GenesisEL el mb)

-- | Which epoch's leadership schedule to query.
data WhichEpoch = CurrentEpoch | NextEpoch
  deriving (Eq, Ord, Read, Show)

-- | Connection / key parameters for the node queries. Mirrors
--   @cardano-cli query leadership-schedule@.
data LeadershipOpts = LeadershipOpts
  { loSocketPath :: FilePath
  , loNetworkId :: Api.NetworkId
  , loGenesisFile :: FilePath
  , loStakePoolId :: (Api.Hash Api.StakePoolKey)
  , loVrfSkeyFile :: FilePath
  , loWhich :: WhichEpoch
  }
--
-- A missing schedule is not fatal: eligibility falls back to the node's own
-- leadership record in the log, so every epoch is still verified. It is reported
-- anyway, because that fallback is the SUT's self-report rather than an independent
-- oracle and so cannot catch the node's leadership logging itself being wrong.
-- One leadership error does not fall back at all — no stake, once the chain is past
-- the two-epoch activation delay, is a known-empty schedule and stronger than the
-- log — so the message is chosen from the resulting schedule, not from the error.
--
-- No waiting: retrying until the query succeeds would not help. Success is not the
-- same as applicability — the node answers for the epoch of its chain tip, which
-- trails the epoch being verified, so a schedule fetched after a wait is usually
-- still for the wrong epoch. Waiting would also let the log accumulate, leaving the
-- verifier further behind and the mismatch more likely.
queryChain :: IORef Bool -> LeadershipOpts -> IO ChainData
queryChain explained opts = do
  (cd, mlerr) <- queryChainOnce opts
  case mlerr of
    Nothing -> pure ()
    Just lerr -> do
      said <- readIORef explained
      if said
        then
          hPutStrLn stderr $
            "no leadership schedule for this epoch either ("
              <> show lerr
              <> "); as above."
        else do
          hPutStrLn stderr (scheduleUnavailable opts lerr (cdWinningSlots cd))
          writeIORef explained True
  pure cd

-- | Explain what the leadership error means and, crucially, what was done about it.
-- Not every such error causes a fallback: past the stake activation delay, no stake
-- is a known-empty schedule rather than a missing one, and saying "continuing from
-- the log" there would contradict the epoch line printed immediately afterwards.
-- The resulting schedule therefore decides which explanation is the true one.
scheduleUnavailable :: LeadershipOpts -> Api.LeadershipError -> Maybe [Integer] -> String
scheduleUnavailable LeadershipOpts{..} lerr mSlots =
  "no leadership schedule for pool "
    <> T.unpack (Api.serialiseToRawBytesHexText loStakePoolId)
    <> ": "
    <> show lerr
    <> ".\n"
    <> case mSlots of
      -- Past the activation delay: "no stake" is the answer, not a gap in it.
      Just _ ->
        "  The chain is past the two-epoch stake activation delay, so this pool\n"
          <> "  genuinely has no stake — not registered, nothing delegated, or the wrong\n"
          <> "  --stake-pool-id. Compare the id above with 'cardano-cli query stake-pools'.\n"
          <> "  Taking the schedule as known-empty, which is stronger than the log: every\n"
          <> "  production obligation is vacuous, so an EB forged here is a real violation."
      Nothing ->
        "  (a) The network may be too young: pool stake takes two epochs to become\n"
          <> "      active, so no schedule exists until the third epoch is under way.\n"
          <> "  (b) That pool may have no stake at all — not registered, nothing\n"
          <> "      delegated, or the wrong --stake-pool-id. Compare the id above with\n"
          <> "      'cardano-cli query stake-pools'.\n"
          <> "  Continuing with eligibility taken from the log instead, which cannot catch\n"
          <> "  an EB forged in a slot the node never recorded winning."

-- | One attempt at the chain query (via the cardano-api local-state-query protocol):
--   the SUT's leadership schedule (the slots in which its pool is an eligible
--   leader) and the on-chain stake distribution, over a single connection. Mirrors
--   cardano-cli's @runQueryLeadershipScheduleCmd@ / @runQueryStakeDistributionCmd@.
--   Returns the data alongside the leadership error, if any: only the schedule part
--   can fail this way, and it is recoverable, so the stake distribution and party
--   count are still delivered. Anything else is fatal here.
queryChainOnce :: LeadershipOpts -> IO (ChainData, Maybe Api.LeadershipError)
queryChainOnce LeadershipOpts{..} = do
  vrfSkey <-
    Api.readFileTextEnvelope @(Api.SigningKey Api.VrfKey) (Api.File loVrfSkeyFile)
      >>= orDie "reading VRF signing key"
  genesisBytes <- BS.readFile loGenesisFile
  (shelleyGenesis :: Api.ShelleyGenesis) <-
    orDie "decoding Shelley genesis" (eitherDecodeStrictText genesisBytes)
  GenesisEL epochLength maxRBBody <-
    orDie
      "reading epochLength and maxBlockBodySize from Shelley genesis"
      (eitherDecodeStrictText genesisBytes)
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
        , Api.EpochNo
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
              expectQueryEra
                "pool distribution"
                (Api.queryPoolDistribution beo (Just (Set.singleton loStakePoolId)))
            stakeDistr <- expectQueryEra "stake distribution" (Api.queryStakeDistribution sbe)
            let schedule =
                  case loWhich of
                    CurrentEpoch ->
                      Api.currentEpochEligibleLeadershipSlots
                        sbe
                        shelleyGenesis
                        eInfo
                        pparams
                        ptclState
                        loStakePoolId
                        vrfSkey
                        serPoolDistr
                        currentEpoch
                    NextEpoch ->
                      error "next-epoch schedule not yet implemented"
            pure (schedule, stakeDistr, currentEpoch)
        )
        era
  case result of
    Left err -> die ("local state query failed: " <> show err)
    Right (eSlots, stakeDistr, nodeEpoch) ->
      let -- Stake registered in epoch e becomes active in epoch e+2, so before
          -- epoch 2 a pool that will have stake still reports as having none. The
          -- error cannot tell the two apart, so the epoch decides which reading is
          -- safe.
          stakeCanHaveActivated = toInteger (Api.unEpochNo nodeEpoch) >= 2
          mSlots = case eSlots of
            -- From epoch 2 on, no active stake is a state rather than a fault: the
            -- schedule is KNOWN empty, every production obligation is vacuous, and
            -- an EB forge would be a genuine violation. Earlier than that the same
            -- error means only "not snapshotted yet", so it is an unknown schedule
            -- like any other leadership error and eligibility comes from the log —
            -- otherwise a devnet pool forging on genesis stake in epoch 0 is
            -- reported as violating EB-Role.
            Left (Api.LeaderErrStakePoolHasNoStake _)
              | stakeCanHaveActivated -> Just []
            Left _ -> Nothing
            Right slots -> Just (Prelude.map (toInteger . Api.unSlotNo) (Set.toList slots))
          mErr = case eSlots of
            Left lerr -> Just lerr
            Right _ -> Nothing
       in pure
            ( buildChainData
                loStakePoolId
                epochLength
                maxRBBody
                (toInteger (Api.unEpochNo nodeEpoch))
                mSlots
                stakeDistr
            , mErr
            )

-- | Turn the on-chain stake distribution (pool-id → relative stake) into the
--   verifier's view: parties are the pools in chain (Map) order, keyed
--   @node-i@; the SUT is the pool given by --stake-pool-id, at its natural
--   index. Relative stakes are scaled to naturals (per billion).
buildChainData ::
  (Api.Hash Api.StakePoolKey) ->
  Integer ->
  Integer ->
  Integer ->
  Maybe [Integer] ->
  Map.Map (Api.Hash Api.StakePoolKey) Rational ->
  ChainData
buildChainData sutPool epochLength maxRBBody nodeEpoch winning m =
  -- A SUT absent from the distribution (no stake at all) joins as a
  -- zero-stake party at the end: keeps the party set total for the spec
  -- side, and the committee arithmetic correctly excludes it.
  let pairs0 = Map.toList m -- sorted by pool-id, deterministic
      pairs
        | Prelude.any ((== sutPool) . fst) pairs0 = pairs0
        | otherwise = pairs0 <> [(sutPool, 0)]
      nodeName i = T.pack ("node-" <> show (i :: Int))
      scaleStake r = floor (r * 1000000000) :: Integer
      stakeDist = [(nodeName i, scaleStake r) | (i, (_, r)) <- Prelude.zip [0 ..] pairs]
      sutIdx =
        maybe (error sutNotFound) toInteger $
          List.findIndex ((== sutPool) . fst) pairs
      sutNotFound =
        "SUT stake pool not found in the chain stake distribution, which lists "
          <> show (Prelude.length pairs)
          <> " pool(s). On a young network the distribution can still be empty, "
          <> "since pool stake takes two epochs to activate; otherwise check "
          <> "--stake-pool-id."
   in ChainData
        { cdWinningSlots = winning
        , cdNumParties = toInteger (Prelude.length pairs)
        , cdStakeDistribution = stakeDist
        , cdSutIndex = sutIdx
        , cdEpochLength = epochLength
        , cdMaxRBBody = maxRBBody
        , cdNodeEpoch = nodeEpoch
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
newtype ChainCommand = ChainCommand
  { leadershipOpts :: LeadershipOpts
  }

commandParser :: ParserInfo ChainCommand
commandParser =
  info (com <**> helper) $
    fullDesc
      <> progDesc "Linear Leios streaming trace verifier (reads schedule and stake distribution from a node via cardano-api)"
      <> header "Leios trace verifier (chain)"
 where
  com = ChainCommand <$> leadershipParser

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

readPoolId :: String -> Either String (Api.Hash Api.StakePoolKey)
readPoolId s =
  case Api.deserialiseFromBech32 (T.pack s) of
    Right (p :: (Api.Hash Api.StakePoolKey)) -> Right p
    Left _ ->
      case Api.deserialiseFromRawBytesHex (BSC.pack s) of
        Right (p :: (Api.Hash Api.StakePoolKey)) -> Right p
        Left e -> Left ("invalid stake pool id: " <> show e)
