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
import Data.Yaml (FromJSON (..), decodeEither', withObject, (.:))
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
    "skipped " <> show (Prelude.length preSlot)
      <> " pre-slot events (node sync/replay backlog, before the first leadership-check slot)"
  runSegmented leadershipOpts (lhdr, lvote, ldiff, validityCheckTime) rest

-- | A verification segment: the part of the trace within one epoch, verified
--   against the schedule and stake distribution queried for that epoch.
data Segment = Segment
  { segEpoch :: Integer
  , segStart :: Integer -- ^ first leadership-check slot of the segment
  , segCD :: ChainData
  }

-- | Verify the node.log stream one epoch-segment at a time. At each epoch
--   boundary the node is re-queried for that epoch's leadership schedule and
--   stake distribution, and a fresh segment is started from the boundary slot —
--   so no process restart is needed and re-verification cost stays bounded per
--   epoch rather than growing over the whole run. This assumes the verifier
--   roughly keeps up with the live node, since a node reports only the current
--   epoch's schedule. Votes that straddle a boundary (an EB from the previous
--   epoch voted in the next) are a known limitation of the hard reset.
runSegmented ::
  LeadershipOpts ->
  (Integer, Integer, Integer, Integer) ->
  [ChainEvent] ->
  IO ()
runSegmented opts (lhdr, lvote, ldiff, validityCheckTime) = loop Nothing []
 where
  loop :: Maybe Segment -> [ChainEvent] -> [ChainEvent] -> IO ()
  loop mseg seen [] = finishSeg mseg (Prelude.reverse seen)
  loop mseg seen (ev : rest) = do
    hPutStrLn stderr $ "event: " <> show ev
    case ev of
      CSlot s -> case mseg of
        Just seg | toInteger s `div` cdEpochLength (segCD seg) == segEpoch seg -> do
          -- same epoch: extend and re-check the current segment
          let seen' = ev : seen
          checkSeg seg (Prelude.reverse seen')
          loop mseg seen' rest
        _ -> do
          -- first segment, or an epoch boundary: (re-)query and start fresh
          seg <- newSegment (toInteger s)
          checkSeg seg [ev]
          loop (Just seg) [ev] rest
      _ -> loop mseg (ev : seen) rest

  newSegment :: Integer -> IO Segment
  newSegment s = do
    cd <- queryChain opts
    setLeadershipSchedule (cdWinningSlots cd)
    let ep = s `div` cdEpochLength cd
    hPutStrLn stderr $
      "epoch " <> show ep <> " (from slot " <> show s <> "): "
        <> show (Prelude.length (cdWinningSlots cd)) <> " winning slots "
        <> show (cdWinningSlots cd) <> ", " <> show (cdNumParties cd)
        <> " parties, SUT at index " <> show (cdSutIndex cd)
    pure Segment{segEpoch = ep, segStart = s, segCD = cd}

  verifySeg :: Segment -> [ChainEvent] -> ([T.Text], (T.Text, T.Text))
  verifySeg seg prefix =
    let cd = segCD seg
     in verifyChainTraceFromSlot (cdNumParties cd) (cdSutIndex cd) (cdStakeDistribution cd)
          lhdr lvote ldiff validityCheckTime prefix (segStart seg)

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
          then hPutStrLn stderr "stream ended: ok" >> printActions acts
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
  , cdEpochLength :: Integer
  -- ^ Slots per epoch (from the Shelley genesis), used to detect epoch
  --   boundaries so the schedule and stake distribution can be re-queried.
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
      pure $ buildChainData loStakePoolId epochLength (Prelude.map (toInteger . Api.unSlotNo) (Set.toList slots)) stakeDistr

-- | Turn the on-chain stake distribution (pool-id → relative stake) into the
--   verifier's view: parties are the pools in chain (Map) order, keyed
--   @node-i@; the SUT is the pool given by --stake-pool-id, at its natural
--   index. Relative stakes are scaled to naturals (per billion).
buildChainData ::
  Api.PoolId ->
  Integer ->
  [Integer] ->
  Map.Map (Api.Hash Api.StakePoolKey) Rational ->
  ChainData
buildChainData sutPool epochLength winning m =
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
        , cdEpochLength = epochLength
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
