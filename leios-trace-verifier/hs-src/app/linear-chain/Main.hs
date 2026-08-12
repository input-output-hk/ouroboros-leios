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
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.Maybe (fromMaybe)
import Data.Yaml (FromJSON (..), decodeEither', withObject, (.:))
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

-- | Run the CLI: stream-verify the node.log from stdin, re-querying the node's
--   leadership schedule and stake distribution at each epoch boundary.
main :: IO ()
main = do
  ChainCommand{..} <- execParser commandParser

  let lhdr = 1
      lvote = 4
      ldiff = 7
      validityCheckTime = 3

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
  runSegmented leadershipOpts (lhdr, lvote, ldiff, validityCheckTime) rest

-- | A verification segment: the part of the trace within one epoch, verified
--   against the schedule and stake distribution queried for that epoch.
data Segment = Segment
  { segEpoch :: Integer
  , segStart :: Integer
  -- ^ first leadership-check slot of the segment
  , segCD :: ChainData
  , segAuthoritative :: Bool
  -- ^ Whether the queried leadership schedule applies to this epoch: obtained at
  --   all, and for this very epoch. Pool stake takes two epochs to become active
  --   (before that the query fails with @LeaderErrStakePoolHasNoStake@) and a node
  --   answers only for its own current epoch, which in practice trails the epoch
  --   being verified. When it does not apply, eligibility is taken from the node's
  --   own leadership record in the log instead, so the segment is still verified.
  }

-- | Verify the node.log stream one epoch-segment at a time. At each epoch
--   boundary the node is re-queried for that epoch's leadership schedule and
--   stake distribution, and a fresh segment is started from the boundary slot —
--   so no process restart is needed and re-verification cost stays bounded per
--   epoch rather than growing over the whole run. A segment does not begin exactly
--   at the boundary, though: it carries 'overlapSlots' of the outgoing epoch with it,
--   so an obligation raised there but falling due after the boundary is still
--   checked. A clean cut would clear EBs' and curEB, and such a vote would then pass
--   vacuously.
--
--   A node can only answer for its own current epoch, and not at all until pool
--   stake has activated two epochs in. A log that starts at genesis therefore
--   always contains epochs whose schedule is unobtainable; those segments are
--   skipped and named rather than verified against the wrong lottery, and the run
--   ends with a summary of which epochs were verified and which were skipped.
runSegmented ::
  LeadershipOpts ->
  (Integer, Integer, Integer, Integer) ->
  [ChainEvent] ->
  IO ()
runSegmented opts (lhdr, lvote, ldiff, validityCheckTime) evs = do
  tally <- newIORef []
  loop tally Nothing [] evs
  summarize tally
 where
  loop :: IORef [(Integer, Bool)] -> Maybe Segment -> [ChainEvent] -> [ChainEvent] -> IO ()
  loop _ mseg seen [] = finishSeg mseg (Prelude.reverse seen)
  loop tally mseg seen (ev : rest) = do
    hPutStrLn stderr $ "event: " <> show ev
    case ev of
      CSlot s -> case mseg of
        Just seg | toInteger s `div` cdEpochLength (segCD seg) == segEpoch seg -> do
          -- same epoch: extend and re-check the current segment
          let seen' = ev : seen
          checkSeg seg (Prelude.reverse seen')
          loop tally mseg seen' rest
        _ -> do
          -- First segment, or an epoch boundary. This CSlot is what completes the
          -- outgoing segment's last slot, so give that segment one final check
          -- with the boundary event appended before discarding its events —
          -- otherwise the last slot of every epoch would go unverified, since a
          -- streaming check never adjudicates the slot still in progress.
          case mseg of
            Just old -> checkSeg old (Prelude.reverse (ev : seen))
            Nothing -> pure ()
          -- Carry the tail of the outgoing epoch into the new segment, so that an
          -- obligation raised before the boundary and falling due after it is still
          -- checked. No check here: the carried slots were just adjudicated by the
          -- outgoing segment, and the boundary slot itself is still in progress.
          let carried = Prelude.takeWhile (notBefore (toInteger s - overlapSlots)) seen
              seen' = ev : carried
              start = earliestSlot (toInteger s) seen'
          seg <- newSegment tally (toInteger s) start (not (Prelude.null carried))
          loop tally (Just seg) seen' rest
      _ -> loop tally mseg (ev : seen) rest

  -- How far back an obligation can reach. An EB with election slot e becomes votable
  -- in slot e + (3 * Lhdr `max` validityCheckTime), and its acquisition may lag the
  -- election by up to Lhdr, so carrying that many slots covers every obligation able
  -- to straddle a boundary.
  overlapSlots :: Integer
  overlapSlots = Prelude.max (3 * lhdr) validityCheckTime + lhdr

  notBefore :: Integer -> ChainEvent -> Bool
  notBefore cutoff (CSlot sl) = toInteger sl >= cutoff
  notBefore _ _ = True

  -- Earliest slot tick among a segment's events, which is where verification starts.
  earliestSlot :: Integer -> [ChainEvent] -> Integer
  earliestSlot dflt es = case [toInteger sl | CSlot sl <- es] of
    [] -> dflt
    ss -> Prelude.minimum ss

  newSegment :: IORef [(Integer, Bool)] -> Integer -> Integer -> Bool -> IO Segment
  newSegment tally boundary start spansEpochs = do
    cd <- queryChain opts
    let ep = boundary `div` cdEpochLength cd
        -- Authoritative only if a schedule was obtained, it describes this very
        -- epoch, and this segment lies wholly inside that epoch. A segment carrying
        -- an overlap spans two, so no single epoch's schedule governs all of it and
        -- eligibility has to come from the log. Otherwise an EB forged in the carried
        -- tail would be judged against the following epoch's lottery.
        authoritative =
          not spansEpochs
            && maybe False (const (ep == cdNodeEpoch cd)) (cdWinningSlots cd)
    reportSchedule cd ep start spansEpochs authoritative
    modifyIORef' tally ((ep, authoritative) :)
    pure Segment{segEpoch = ep, segStart = start, segCD = cd, segAuthoritative = authoritative}

  reportSchedule :: ChainData -> Integer -> Integer -> Bool -> Bool -> IO ()
  reportSchedule cd ep s spansEpochs authoritative = do
    hPutStrLn stderr $
      "epoch "
        <> show ep
        <> " (from slot "
        <> show s
        <> (if spansEpochs then ", carrying the tail of the previous epoch" else "")
        <> "): "
        <> show (cdNumParties cd)
        <> " parties, SUT at index "
        <> show (cdSutIndex cd)
        <> ", eligibility from "
        <> source
    when authoritative (warnSlotsOutsideEpoch cd ep)
   where
    source = case cdWinningSlots cd of
      Nothing -> "the log (the node could supply no schedule)"
      Just slots
        | authoritative ->
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

  -- The node claims this epoch, so its winning slots ought to lie inside it. If any
  -- do not, an assumption is wrong — epochLength, or which epoch the schedule is
  -- computed for — and this segment is being verified unsoundly. Report loudly
  -- rather than refuse: refusing has already proved too blunt, and this is precisely
  -- the diagnostic needed to tell which assumption is off.
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

  -- Every segment is verified now, so the interesting distinction is which
  -- eligibility source each epoch used. A log-derived one cannot catch an EB forged
  -- in a slot the node never recorded winning, so it is worth knowing where the
  -- guarantee is weaker.
  summarize :: IORef [(Integer, Bool)] -> IO ()
  summarize tally = do
    entries <- Prelude.reverse <$> readIORef tally
    let fromSchedule = [ep | (ep, True) <- entries]
        fromLog = [ep | (ep, False) <- entries]
    if Prelude.null entries
      then hPutStrLn stderr "summary: no segment was verified"
      else
        hPutStrLn stderr $
          "summary: verified epoch(s) "
            <> show (Prelude.map fst entries)
            <> "; eligibility from the node schedule for "
            <> (if Prelude.null fromSchedule then "none" else show fromSchedule)
            <> ", from the log for "
            <> (if Prelude.null fromLog then "none" else show fromLog)

  verifySeg :: Segment -> [ChainEvent] -> ([T.Text], (T.Text, T.Text))
  verifySeg seg prefix =
    let cd = segCD seg
     in verifyChainTraceFromSlot
          (cdNumParties cd)
          (cdSutIndex cd)
          (cdStakeDistribution cd)
          lhdr
          lvote
          ldiff
          validityCheckTime
          (fromMaybe [] (cdWinningSlots cd))
          (segAuthoritative seg)
          prefix
          (segStart seg)

  checkSeg :: Segment -> [ChainEvent] -> IO ()
  checkSeg seg prefix =
    let (acts, (status, detail)) = verifySeg seg prefix
     in if status == "ok"
          then hPutStrLn stderr $ "ok @ " <> show (Prelude.length prefix) <> " events, " <> show (Prelude.length acts) <> " actions"
          else failOut prefix acts status detail

  finishSeg :: Maybe Segment -> [ChainEvent] -> IO ()
  finishSeg Nothing _ = hPutStrLn stderr "no leadership-check slot found in input — nothing to verify"
  finishSeg (Just seg) prefix =
    let (acts, (status, detail)) = verifySeg seg prefix
     in if status == "ok"
          then
            -- The slot in progress when the input ended is deliberately not
            -- adjudicated: a stream truncated mid-slot has not yet shown the
            -- events that would discharge that slot's obligations.
            hPutStrLn stderr "stream ended: ok (slot in progress at end of input left unverified)"
              >> printActions acts
          else failOut prefix acts status detail

  printActions = mapM_ (\a -> hPutStrLn stderr ("  action: " <> T.unpack a))
  -- The slot an action or error status belongs to.
  slotOfAction a = T.takeWhile (/= ' ') (T.drop 1 (T.dropWhile (/= '@') a))
  failOut prefix acts status detail = do
    hPutStrLn stderr $
      "VIOLATION after " <> show (Prelude.length prefix) <> " events: " <> T.unpack status
    hPutStrLn stderr $ T.unpack detail
    when ("Err-Invalid" `T.isInfixOf` status) $
      hPutStrLn stderr $
        "  (Err-Invalid: a No-EB-Role/No-VT-Role abstention was rejected — the spec "
          <> "permits abstaining only when the role cannot be performed this slot.)"
    -- Only the actions in the failing slot.
    let failSlot = T.takeWhile (/= ' ') status
    printActions (Prelude.filter ((== failSlot) . slotOfAction) acts)
    exitFailure

-- | True iff the event is a slot tick (used as a re-verification checkpoint).
isCSlot :: ChainEvent -> Bool
isCSlot (CSlot _) = True
isCSlot _ = False

-- * Reading from the chain via cardano-api

-- | Minimal view of the Shelley genesis: just the epoch length (slots/epoch).
newtype GenesisEL = GenesisEL Integer

instance FromJSON GenesisEL where
  parseJSON = withObject "ShelleyGenesis" $ \o -> GenesisEL <$> o .: "epochLength"

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

-- | Everything we read from the chain for verification.
data ChainData = ChainData
  { cdWinningSlots :: Maybe [Integer]
  -- ^ The SUT's leadership schedule, as plain naturals for the Agda oracle.
  --   'Nothing' when the node could not supply one at all — chiefly on a young
  --   network, where pool stake has not activated yet. Not fatal: eligibility then
  --   comes from the node's own leadership record in the log.
  , cdNumParties :: Integer
  -- ^ Number of parties (= number of stake pools).
  , cdStakeDistribution :: [(T.Text, Integer)]
  -- ^ Per-party stake, keyed @node-i@ (pool i in chain order).
  , cdSutIndex :: Integer
  -- ^ The SUT's party index (position of --stake-pool-id in chain order).
  , cdEpochLength :: Integer
  -- ^ Slots per epoch (from the Shelley genesis), used to detect epoch
  --   boundaries so the schedule and stake distribution can be re-queried.
  , cdNodeEpoch :: Integer
  -- ^ The epoch the node itself reported when queried, i.e. the epoch the
  --   returned schedule belongs to. This is the epoch of the /chain tip/ (the
  --   query runs at 'Api.VolatileTip'), not of the wall clock, so it lags
  --   whenever block production is sparse — which is one way the schedule ends
  --   up describing a different epoch than the one being verified.
  }

-- | Query the chain for the leadership schedule, stake distribution and party count.
--
-- A missing schedule is not fatal: eligibility falls back to the node's own
-- leadership record in the log, so every epoch is still verified. It is reported
-- anyway, because that fallback is the SUT's self-report rather than an independent
-- oracle and so cannot catch the node's leadership logging itself being wrong.
--
-- No waiting: retrying until the query succeeds would not help. Success is not the
-- same as applicability — the node answers for the epoch of its chain tip, which
-- trails the epoch being verified, so a schedule fetched after a wait is usually
-- still for the wrong epoch. Waiting would also let the log accumulate, leaving the
-- verifier further behind and the mismatch more likely.
queryChain :: LeadershipOpts -> IO ChainData
queryChain opts = do
  (cd, mlerr) <- queryChainOnce opts
  case mlerr of
    Nothing -> pure ()
    Just lerr -> hPutStrLn stderr (scheduleUnavailable opts lerr)
  pure cd

-- | Explain why no authoritative schedule could be had. Two quite different
-- situations produce it and they call for different responses, so name both.
scheduleUnavailable :: LeadershipOpts -> Api.LeadershipError -> String
scheduleUnavailable LeadershipOpts{..} lerr =
  "no leadership schedule for pool "
    <> T.unpack (Api.serialiseToRawBytesHexText loStakePoolId)
    <> ": "
    <> show lerr
    <> ".\n"
    <> "  (a) The network may be too young: pool stake takes two epochs to become\n"
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
  GenesisEL epochLength <-
    orDie "reading epochLength from Shelley genesis" (eitherDecodeStrictText genesisBytes)
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
      let mSlots = case eSlots of
            Left _ -> Nothing
            Right slots -> Just (Prelude.map (toInteger . Api.unSlotNo) (Set.toList slots))
          mErr = case eSlots of
            Left lerr -> Just lerr
            Right _ -> Nothing
       in pure
            ( buildChainData
                loStakePoolId
                epochLength
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
  Maybe [Integer] ->
  Map.Map (Api.Hash Api.StakePoolKey) Rational ->
  ChainData
buildChainData sutPool epochLength nodeEpoch winning m =
  let pairs = Map.toList m -- sorted by pool-id, deterministic
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
