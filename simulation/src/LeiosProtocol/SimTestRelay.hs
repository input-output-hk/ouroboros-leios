{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# HLINT ignore "Use void" #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module LeiosProtocol.SimTestRelay where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TQueue,
    TVar,
    atomically,
    modifyTVar',
    newTQueueIO,
    newTVarIO,
    readTQueue,
    readTVar,
    retry,
    writeTQueue,
    writeTVar
  ),
 )
import Control.Monad (forever)
import Control.Monad.Class.MonadAsync (
  Concurrently (Concurrently, runConcurrently),
  MonadAsync (concurrently_),
 )
import Control.Monad.Class.MonadTime.SI (
  DiffTime,
  MonadTime (..),
  NominalDiffTime,
  Time,
  UTCTime,
  addUTCTime,
  diffUTCTime,
 )
import Control.Monad.Class.MonadTimer (MonadDelay)
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer,
  traceWith,
 )
import Data.Foldable (traverse_)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.Random (StdGen, uniform, uniformR)

import Chan
import ChanTCP
import SimTCPLinks (labelDirToLabelLink, selectTimedEvents, simTracer)
import SimTypes
import TimeCompat (threadDelayNDT, threadDelaySI)

import ChanMux
import Control.Exception (assert)
import Data.Foldable (forM_)
import Data.List (sortOn)
import Data.Ord (Down (..))
import LeiosProtocol.Relay
import LeiosProtocol.RelayBuffer (RelayBuffer)
import qualified LeiosProtocol.RelayBuffer as RB
import PraosProtocol.Common (asReadOnly)

type RelaySimTrace = [(Time, RelaySimEvent)]

data RelaySimEvent
  = -- | Declare the nodes and links
    RelaySimEventSetup
      !WorldShape
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    RelaySimEventNode (LabelNode (RelayNodeEvent TestBlock))
  | -- | An event on a tcp link between two nodes
    RelaySimEventTcp (LabelLink (TcpEvent TestBlockRelayMessage))
  deriving (Show)

data RelayNodeEvent blk
  = RelayNodeEventGenerate blk
  | RelayNodeEventEnterQueue blk
  | RelayNodeEventEnterBuffer blk
  | RelayNodeEventRemove blk
  deriving (Show)

data TestBlock = TestBlock
  { testBlockId :: TestBlockId
  , testBlockSize :: Bytes
  , testBlockExpiry :: TestBlockExpiry
  }
  deriving (Show)

newtype TestBlockId = TestBlockId Int
  deriving (Eq, Ord, Bounded, Enum, Show)

type TestBlockExpiry = UTCTime
type TestBlockLifetime = NominalDiffTime

instance MessageSize TestBlockId where
  messageSizeBytes _ = 32 {- hash/id -}
instance MessageSize TestBlock where
  messageSizeBytes = testBlockSize
instance MessageSize TestBlockHeader where
  messageSizeBytes _ = 32 {- hash/id -} + 8 {- slot no/expiry time -}

-- Using the header/body terminology from LeiosProtocol.Relay, but
-- actually TestBlockHeader here is just meant to be enough
-- information to identify what we want to fetch first.
data TestBlockHeader = TestBlockHeader {testHeaderId :: TestBlockId, testHeaderExpiry :: TestBlockExpiry}
  deriving (Show)
type TestBlockBody = TestBlock -- a bit redundant.
type TestBlockRelayMessage = RelayMessage TestBlockId TestBlockHeader TestBlock

data RelayNodeConfig = RelayNodeConfig
  { blockProcessingDelay :: TestBlock -> DiffTime
  , blockGeneration :: PacketGenerationPattern
  }

data PacketGenerationPattern
  = NoPacketGeneration
  | UniformGenerationPattern Bytes DiffTime TestBlockLifetime
  | PoissonGenerationPattern Bytes StdGen Double TestBlockLifetime

type TestRelayBuffer m = TVar m (RelayBuffer TestBlockId (TestBlockHeader, TestBlockBody))

relayNode ::
  forall m.
  (MonadAsync m, MonadDelay m, MonadTime m) =>
  Tracer m (RelayNodeEvent TestBlock) ->
  RelayNodeConfig ->
  -- | incomming edges
  [Chan m TestBlockRelayMessage] ->
  -- | outgoing edges
  [Chan m TestBlockRelayMessage] ->
  m ()
relayNode
  tracer
  RelayNodeConfig
    { blockProcessingDelay
    , blockGeneration
    }
  inchans
  outchans = do
    buffer <- newTVarIO RB.empty
    inFlightVar <- newTVarIO Set.empty
    submitq <- newTQueueIO :: m (TQueue m ([TestBlock], [TestBlock] -> STM m ()))

    let relayBufferVar = buffer
    let consumerSST = RelayConsumerSharedState{relayBufferVar, inFlightVar}
    let producerSST = RelayProducerSharedState{relayBufferVar = asReadOnly relayBufferVar}
    let relayConfig = RelayConfig{maxWindowSize = 10}
    let relayConsumerConfig =
          RelayConsumerConfig
            { relay = relayConfig
            , headerId = testHeaderId
            , prioritize = sortOn (Down . testHeaderExpiry) . Map.elems
            , submitPolicy = SubmitAll
            , maxHeadersToRequest = relayConfig.maxWindowSize.value
            , maxBodiesToRequest = 1 -- let pipelining stream them.
            , submitBlocks = \blks _ completion ->
                assert (length blks == 1) $ do
                  forM_ blks $ \blk -> traceWith tracer (RelayNodeEventEnterQueue (snd blk))
                  atomically $ writeTQueue submitq (map snd blks, completion . map (\blk -> (testHeader blk, blk)))
            }

    let clients = map (runRelayConsumer relayConsumerConfig consumerSST) inchans
        servers = map (runRelayProducer relayConfig producerSST) outchans

    -- WARNING: Concurrently not suitable for large sims.
    runConcurrently $
      ()
        <$ Concurrently (generation buffer)
        <* Concurrently (pruning buffer)
        <* Concurrently (processing submitq)
        <* traverse_ Concurrently clients
        <* traverse_ Concurrently servers
   where
    addBlock b =
      assert (testBlockId b == testHeaderId (testHeader b)) $
        RB.snoc (testBlockId b) (testHeader b, b)
    generation :: TestRelayBuffer m -> m ()
    generation buffer = case blockGeneration of
      NoPacketGeneration -> return ()
      UniformGenerationPattern sz gendelay blklifetime ->
        go (TestBlockId 0)
       where
        -- TODO: make different generators produce different non-overlapping ids
        go !blkid = do
          threadDelaySI gendelay
          now <- getCurrentTime
          let blk =
                TestBlock
                  { testBlockId = blkid
                  , testBlockSize = sz
                  , testBlockExpiry = blklifetime `addUTCTime` now
                  }
          atomically $
            modifyTVar' buffer (addBlock blk)
          traceWith tracer (RelayNodeEventGenerate blk)
          go (succ blkid)
      PoissonGenerationPattern sz rng0 lambda blklifetime ->
        go rng0
       where
        go !rng = do
          let (u, rng') = uniformR (0, 1) rng
              gendelay = realToFrac ((-log u) * lambda :: Double) :: DiffTime
          threadDelaySI gendelay
          now <- getCurrentTime
          let (blkidn, rng'') = uniform rng'
              blkid = TestBlockId blkidn
              blk =
                TestBlock
                  { testBlockId = blkid
                  , testBlockSize = sz
                  , testBlockExpiry = blklifetime `addUTCTime` now -- TODO: round to seconds.
                  }
          atomically $
            modifyTVar' buffer (addBlock blk)
          traceWith tracer (RelayNodeEventGenerate blk)
          go rng''

    pruning :: TestRelayBuffer m -> m ()
    pruning buffer =
      -- note that this is imperfect, it crudly assumes the lowest ticket no
      -- will have the earliest expiry time, which is not necessarily true.
      -- So some out-of-order packets will expire late. Shouldn't be a problem.
      forever $ do
        expiry <- atomically $ do
          blkq <- readTVar buffer
          case RB.uncons blkq of
            Nothing -> retry
            Just (blk, _) -> return (testBlockExpiry (snd blk))
        now <- getCurrentTime
        threadDelayNDT (expiry `diffUTCTime` now)
        blks <- atomically $ do
          blkq <- readTVar buffer
          let (blks, !blkq') = dequeueExpired expiry [] blkq
          writeTVar buffer blkq'
          return blks
        mapM_ (traceWith tracer . RelayNodeEventRemove . snd) blks
     where
      dequeueExpired expiry blks blkq =
        case RB.uncons blkq of
          Nothing -> (blks, blkq)
          Just (blk, blkq')
            | testBlockExpiry (snd blk) <= expiry ->
                dequeueExpired expiry (blk : blks) blkq'
            | otherwise -> (blks, blkq)

    processing :: TQueue m ([TestBlock], [TestBlock] -> STM m a) -> m ()
    processing submitq =
      forever $ do
        (blks, completion) <- atomically $ readTQueue submitq
        threadDelaySI (sum $ map blockProcessingDelay blks)
        _ <- atomically $ completion blks -- "relayNode: completions should not block"
        forM_ blks $ \blk -> traceWith tracer (RelayNodeEventEnterBuffer blk)

testHeader :: TestBlock -> TestBlockHeader
testHeader blk = TestBlockHeader (testBlockId blk) (testBlockExpiry blk)

symmetric :: Ord a => Set (a, a) -> Set (a, a)
symmetric xys = xys <> Set.map (\(x, y) -> (y, x)) xys

data TestRelayBundle f = TestRelayBundle
  { testMsg :: f TestBlockRelayMessage
  }

instance MuxBundle TestRelayBundle where
  type MuxMsg TestRelayBundle = TestBlockRelayMessage

  toFromMuxMsgBundle =
    TestRelayBundle
      { testMsg = ToFromMuxMsg id id
      }

  traverseMuxBundle f TestRelayBundle{..} =
    TestRelayBundle
      <$> f testMsg

traceRelayLink1 ::
  TcpConnProps ->
  PacketGenerationPattern ->
  RelaySimTrace
traceRelayLink1 tcpprops generationPattern =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        RelaySimEventSetup
          WorldShape
            { worldDimensions = (500, 500)
            , worldIsCylinder = False
            }
          ( Map.fromList
              [ (NodeId 0, Point 50 100)
              , (NodeId 1, Point 450 100)
              ]
          )
          ( Set.fromList
              [(NodeId 0, NodeId 1), (NodeId 1, NodeId 0)]
          )
      (TestRelayBundle inChan, TestRelayBundle outChan) <- newConnectionBundleTCP (linkTracer na nb) tcpprops
      concurrently_
        (relayNode (nodeTracer na) configNode0 [] [inChan])
        (relayNode (nodeTracer nb) configNode1 [outChan] [])
 where
  [na, nb] = map NodeId [0, 1]
  configNode0 = RelayNodeConfig processingDelay generationPattern
  configNode1 = RelayNodeConfig processingDelay NoPacketGeneration
  processingDelay = const 0.1 -- 100 ms
  tracer :: Tracer (IOSim s) RelaySimEvent
  tracer = simTracer

  nodeTracer :: NodeId -> Tracer (IOSim s) (RelayNodeEvent TestBlock)
  nodeTracer n =
    contramap (RelaySimEventNode . LabelNode n) tracer

  linkTracer ::
    NodeId ->
    NodeId ->
    Tracer
      (IOSim s)
      (LabelTcpDir (TcpEvent TestBlockRelayMessage))
  linkTracer nfrom nto =
    contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer

traceRelayLink4 ::
  TcpConnProps ->
  PacketGenerationPattern ->
  RelaySimTrace
traceRelayLink4 tcpprops generationPattern =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        RelaySimEventSetup
          WorldShape
            { worldDimensions = (1000, 500)
            , worldIsCylinder = False
            }
          ( Map.fromList
              [ (NodeId 0, Point 50 250)
              , (NodeId 1, Point 450 70)
              , (NodeId 2, Point 550 430)
              , (NodeId 3, Point 950 250)
              ]
          )
          ( symmetric $
              Set.fromList
                [ (NodeId 0, NodeId 1)
                , (NodeId 1, NodeId 3)
                , (NodeId 0, NodeId 2)
                , (NodeId 2, NodeId 3)
                ]
          )
      (TestRelayBundle a2bInChan, TestRelayBundle a2bOutChan) <- newConnectionBundleTCP (linkTracer na nb) tcpprops
      (TestRelayBundle a2cInChan, TestRelayBundle a2cOutChan) <- newConnectionBundleTCP (linkTracer na nc) tcpprops
      (TestRelayBundle b2dInChan, TestRelayBundle b2dOutChan) <- newConnectionBundleTCP (linkTracer nb nd) tcpprops
      (TestRelayBundle c2dInChan, TestRelayBundle c2dOutChan) <- newConnectionBundleTCP (linkTracer nc nd) tcpprops
      let generator n = relayNode (nodeTracer n) configGen
          relay n = relayNode (nodeTracer n) configRelay
      runConcurrently $
        ()
          <$ Concurrently (generator na [] [a2bInChan, a2cInChan])
          <* Concurrently (relay nb [a2bOutChan] [b2dInChan])
          <* Concurrently (relay nc [a2cOutChan] [c2dInChan])
          <* Concurrently (relay nd [b2dOutChan, c2dOutChan] [])
 where
  [na, nb, nc, nd] = map NodeId [0 .. 3]
  configGen = RelayNodeConfig processingDelay generationPattern
  configRelay = RelayNodeConfig processingDelay NoPacketGeneration
  processingDelay = const 0.1 -- 100 ms
  tracer :: Tracer (IOSim s) RelaySimEvent
  tracer = simTracer

  nodeTracer :: NodeId -> Tracer (IOSim s) (RelayNodeEvent TestBlock)
  nodeTracer n =
    contramap (RelaySimEventNode . LabelNode n) tracer

  linkTracer ::
    NodeId ->
    NodeId ->
    Tracer
      (IOSim s)
      (LabelTcpDir (TcpEvent TestBlockRelayMessage))
  linkTracer nfrom nto =
    contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer

traceRelayLink4Asymmetric ::
  TcpConnProps ->
  TcpConnProps ->
  PacketGenerationPattern ->
  RelaySimTrace
traceRelayLink4Asymmetric tcppropsShort tcppropsLong generationPattern =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        RelaySimEventSetup
          WorldShape
            { worldDimensions = (1000, 500)
            , worldIsCylinder = False
            }
          ( Map.fromList
              [ (NodeId 0, Point 50 70)
              , (NodeId 1, Point 450 400)
              , (NodeId 2, Point 500 70)
              , (NodeId 3, Point 950 70)
              ]
          )
          ( symmetric $
              Set.fromList
                [ (NodeId 0, NodeId 1)
                , (NodeId 1, NodeId 3)
                , (NodeId 0, NodeId 2)
                , (NodeId 2, NodeId 3)
                ]
          )
      (TestRelayBundle a2bInChan, TestRelayBundle a2bOutChan) <- newConnectionBundleTCP (linkTracer na nb) tcppropsLong
      (TestRelayBundle a2cInChan, TestRelayBundle a2cOutChan) <- newConnectionBundleTCP (linkTracer na nc) tcppropsShort
      (TestRelayBundle b2dInChan, TestRelayBundle b2dOutChan) <- newConnectionBundleTCP (linkTracer nb nd) tcppropsLong
      (TestRelayBundle c2dInChan, TestRelayBundle c2dOutChan) <- newConnectionBundleTCP (linkTracer nc nd) tcppropsShort
      let generator n = relayNode (nodeTracer n) configGen
          relay n = relayNode (nodeTracer n) configRelay
      runConcurrently $
        ()
          <$ Concurrently (generator na [] [a2bInChan, a2cInChan])
          <* Concurrently (relay nb [a2bOutChan] [b2dInChan])
          <* Concurrently (relay nc [a2cOutChan] [c2dInChan])
          <* Concurrently (relay nd [b2dOutChan, c2dOutChan] [])
 where
  [na, nb, nc, nd] = map NodeId [0 .. 3]
  configGen = RelayNodeConfig processingDelay generationPattern
  configRelay = RelayNodeConfig processingDelay NoPacketGeneration
  processingDelay = const 0.1 -- 100 ms
  tracer :: Tracer (IOSim s) RelaySimEvent
  tracer = simTracer

  nodeTracer :: NodeId -> Tracer (IOSim s) (RelayNodeEvent TestBlock)
  nodeTracer n =
    contramap (RelaySimEventNode . LabelNode n) tracer

  linkTracer ::
    NodeId ->
    NodeId ->
    Tracer
      (IOSim s)
      (LabelTcpDir (TcpEvent TestBlockRelayMessage))
  linkTracer nfrom nto =
    contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer
