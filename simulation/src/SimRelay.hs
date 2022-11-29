{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module SimRelay where

import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Foldable

import Control.Applicative
import Control.Monad
import Control.Monad.Class.MonadTime
import Control.Monad.Class.MonadTimer
import Control.Monad.Class.MonadAsync
import Control.Concurrent.Class.MonadSTM
import Control.Tracer as Tracer

import Control.Monad.IOSim as IOSim

import System.Random (StdGen, uniformR, uniform)

import Chan
import RelayProtocol
import ChanTCP
import SimTypes
import SimTCPLinks (simTracer, labelDirToLabelLink, selectTimedEvents)


type RelaySimTrace = [(Time, RelaySimEvent)]

data RelaySimEvent =
       -- | Declare the nodes and links
       RelaySimEventSetup
         !WorldShape
         !(Map NodeId Point)            -- nodes and locations
         !(Set (NodeId, NodeId))        -- links between nodes

       -- | An event at a node
     | RelaySimEventNode (LabelNode (RelayNodeEvent TestBlock))

       -- | An event on a tcp link between two nodes
     | RelaySimEventTcp (LabelLink (TcpEvent TestBlockRelayMessage))
  deriving Show

data RelayNodeEvent blk =
       RelayNodeEventGenerate    blk
     | RelayNodeEventEnterQueue  blk
     | RelayNodeEventEnterBuffer blk
     | RelayNodeEventRemove      blk
  deriving Show

data TestBlock = TestBlock {
                   testBlockId     :: TestBlockId,
                   testBlockSize   :: Bytes,
                   testBlockExpiry :: TestBlockExpiry
                 }
  deriving (Show)

newtype TestBlockId = TestBlockId Int
  deriving (Eq, Ord, Bounded, Enum, Show)

type TestBlockExpiry   = UTCTime
type TestBlockLifetime = NominalDiffTime

instance MessageSize TestBlock where
    messageSizeBytes = testBlockSize

type TestBlockRelayMessage = BlockRelayMessage TestBlock TestBlockId BlockTTL

data RelayNodeConfig =
     RelayNodeConfig {
       blockProcessingDelay :: TestBlock -> DiffTime,
       blockGeneration      :: PacketGenerationPattern
     }

data PacketGenerationPattern =
       NoPacketGeneration
     | UniformGenerationPattern Bytes DiffTime TestBlockLifetime
     | PoissonGenerationPattern Bytes StdGen Double TestBlockLifetime

relayNode :: forall m.
             (MonadAsync m, MonadDelay m, MonadTime m)
          => Tracer m (RelayNodeEvent TestBlock)
          -> RelayNodeConfig
          -> [Chan m TestBlockRelayMessage] -- ^ incomming edges
          -> [Chan m TestBlockRelayMessage] -- ^ outgoing edges
          -> m ()
relayNode tracer
          RelayNodeConfig {
            blockProcessingDelay,
            blockGeneration
          }
          inchans outchans = do
    buffer   <- newRelayBuffer
    inflight <- newTVarIO Set.empty
    submitq  <- newTQueueIO :: m (TQueue m (TestBlock, STM m ()))

    let relayconfig :: BlockRelayConfig m TestBlock TestBlockId
        relayconfig =
          BlockRelayConfig {
            blockId      = testBlockId,
            blockTTL     = BlockTTL . testBlockExpiry,
            submitBlock = \blk completion -> do
                             traceWith tracer (RelayNodeEventEnterQueue blk)
                             atomically $ writeTQueue submitq (blk, completion)
          }

    let clients = map (relayClient relayconfig buffer inflight) inchans
        servers = map (relayServer relayconfig buffer) outchans

    runConcurrently $
      () <$ Concurrently (generation buffer)
         <* Concurrently (pruning buffer)
         <* Concurrently (processing submitq)
         <* traverse_ Concurrently clients
         <* traverse_ Concurrently servers
  where
    generation :: RelayBuffer m TestBlock TestBlockId -> m ()
    generation buffer = case blockGeneration of
      NoPacketGeneration -> return ()
      UniformGenerationPattern sz gendelay blklifetime ->
          go (TestBlockId 0)
          --TODO: make different generators produce different non-overlapping ids
        where
          go !blkid = do
            threadDelay gendelay
            now <- getCurrentTime
            let blk = TestBlock { 
                        testBlockId     = blkid,
                        testBlockSize   = sz,
                        testBlockExpiry = blklifetime `addUTCTime` now
                      }
            atomically $
              modifyRelayBuffer buffer $ \q -> snocBlockQueue blk blkid q
            traceWith tracer (RelayNodeEventGenerate blk)
            go (succ blkid)
      PoissonGenerationPattern sz rng0 lambda blklifetime ->
          go rng0
        where
          go !rng = do
            let (u, rng') = uniformR (0,1) rng
                gendelay  = realToFrac (- log u * lambda :: Double) :: DiffTime
            threadDelay gendelay
            now <- getCurrentTime
            let (blkidn, rng'') = uniform rng'
                blkid = TestBlockId blkidn
                blk = TestBlock { 
                        testBlockId     = blkid,
                        testBlockSize   = sz,
                        testBlockExpiry = blklifetime `addUTCTime` now
                      }
            atomically $
              modifyRelayBuffer buffer $ \q -> snocBlockQueue blk blkid q
            traceWith tracer (RelayNodeEventGenerate blk)
            go rng''

    pruning :: RelayBuffer m TestBlock TestBlockId -> m ()
    pruning (RelayBuffer buffer) =
      -- note that this is imperfect, it crudly assumes the lowest ticket no
      -- will have the earliest expiry time, which is not necessarily true.
      -- So some out-of-order packets will expire late. Shouldn't be a problem.
      forever $ do
        expiry <- atomically $ do
          blkq <- readTVar buffer
          case unconsBlockQueue blkq of
            Nothing -> retry
            Just (blk, _) -> return (testBlockExpiry blk)
        now <- getCurrentTime
        threadDelay (realToFrac (expiry `diffUTCTime` now))
        blks <- atomically $ do
          blkq <- readTVar buffer
          let (blks, !blkq') = dequeueExpired expiry [] blkq
          writeTVar buffer blkq'
          return blks
        mapM_ (traceWith tracer . RelayNodeEventRemove) blks
      where
        dequeueExpired expiry blks blkq =
          case unconsBlockQueue blkq of
            Nothing       -> (blks, blkq)
            Just (blk, blkq')
              | testBlockExpiry blk <= expiry
                          -> dequeueExpired expiry (blk:blks) blkq'
              | otherwise -> (blks, blkq)

    processing :: TQueue m (TestBlock, STM m a) -> m ()
    processing submitq =
      forever $ do
        (blk, completion) <- atomically $ readTQueue submitq
        threadDelay (blockProcessingDelay blk)
        _ <- atomically (completion <|> error "relayNode: completions should not block")
        traceWith tracer (RelayNodeEventEnterBuffer blk)

symmetric :: Ord a => Set (a, a) -> Set (a, a)
symmetric xys = xys <> Set.map (\(x,y) -> (y,x)) xys

traceRelayLink1 :: TcpConnProps
                -> PacketGenerationPattern
                -> RelaySimTrace
traceRelayLink1 tcpprops generationPattern =
    selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        RelaySimEventSetup
          WorldShape {
            worldDimensions = (500, 500)
          }
          (Map.fromList
            [(NodeId 0, (Point 50  100)),
             (NodeId 1, (Point 450 100))])
          (Set.fromList
            [(NodeId 0, NodeId 1), (NodeId 1, NodeId 0)])
      (inChan, outChan) <- newConnectionTCP (linkTracer na nb) tcpprops
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

    linkTracer :: NodeId -> NodeId
               -> Tracer (IOSim s)
                         (LabelTcpDir (TcpEvent TestBlockRelayMessage))
    linkTracer nfrom nto =
      contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer

traceRelayLink4 :: TcpConnProps
                -> PacketGenerationPattern
                -> RelaySimTrace
traceRelayLink4 tcpprops generationPattern =
    selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        RelaySimEventSetup
          WorldShape {
            worldDimensions = (1000, 500)
          }
          (Map.fromList
            [(NodeId 0, (Point  50 250)),
             (NodeId 1, (Point 450 70)),
             (NodeId 2, (Point 550 430)),
             (NodeId 3, (Point 950 250))])
          (symmetric $ Set.fromList
            [(NodeId 0, NodeId 1),
             (NodeId 1, NodeId 3),
             (NodeId 0, NodeId 2),
             (NodeId 2, NodeId 3)])
      (a2bInChan, a2bOutChan) <- newConnectionTCP (linkTracer na nb) tcpprops
      (a2cInChan, a2cOutChan) <- newConnectionTCP (linkTracer na nc) tcpprops
      (b2dInChan, b2dOutChan) <- newConnectionTCP (linkTracer nb nd) tcpprops
      (c2dInChan, c2dOutChan) <- newConnectionTCP (linkTracer nc nd) tcpprops
      let generator n = relayNode (nodeTracer n) configGen
          relay     n = relayNode (nodeTracer n) configRelay
      runConcurrently $
        () <$ Concurrently (generator na [] [a2bInChan, a2cInChan])
           <* Concurrently (relay     nb [a2bOutChan] [b2dInChan])
           <* Concurrently (relay     nc [a2cOutChan] [c2dInChan])
           <* Concurrently (relay     nd [b2dOutChan, c2dOutChan] [])
  where
    [na, nb, nc, nd] = map NodeId [0..3]
    configGen   = RelayNodeConfig processingDelay generationPattern
    configRelay = RelayNodeConfig processingDelay NoPacketGeneration
    processingDelay = const 0.1 -- 100 ms

    tracer :: Tracer (IOSim s) RelaySimEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) (RelayNodeEvent TestBlock)
    nodeTracer n =
      contramap (RelaySimEventNode . LabelNode n) tracer

    linkTracer :: NodeId -> NodeId
               -> Tracer (IOSim s)
                         (LabelTcpDir (TcpEvent TestBlockRelayMessage))
    linkTracer nfrom nto =
      contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer

traceRelayLink4Asymmetric :: TcpConnProps
                          -> TcpConnProps
                          -> PacketGenerationPattern
                          -> RelaySimTrace
traceRelayLink4Asymmetric tcppropsShort tcppropsLong generationPattern =
    selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        RelaySimEventSetup
          WorldShape {
            worldDimensions = (1000, 500)
          }
          (Map.fromList
            [(NodeId 0, (Point  50 70)),
             (NodeId 1, (Point 450 400)),
             (NodeId 2, (Point 500 70)),
             (NodeId 3, (Point 950 70))])
          (symmetric $ Set.fromList
            [(NodeId 0, NodeId 1),
             (NodeId 1, NodeId 3),
             (NodeId 0, NodeId 2),
             (NodeId 2, NodeId 3)])
      (a2bInChan, a2bOutChan) <- newConnectionTCP (linkTracer na nb) tcppropsLong
      (a2cInChan, a2cOutChan) <- newConnectionTCP (linkTracer na nc) tcppropsShort
      (b2dInChan, b2dOutChan) <- newConnectionTCP (linkTracer nb nd) tcppropsLong
      (c2dInChan, c2dOutChan) <- newConnectionTCP (linkTracer nc nd) tcppropsShort
      let generator n = relayNode (nodeTracer n) configGen
          relay     n = relayNode (nodeTracer n) configRelay
      runConcurrently $
        () <$ Concurrently (generator na [] [a2bInChan, a2cInChan])
           <* Concurrently (relay     nb [a2bOutChan] [b2dInChan])
           <* Concurrently (relay     nc [a2cOutChan] [c2dInChan])
           <* Concurrently (relay     nd [b2dOutChan, c2dOutChan] [])
  where
    [na, nb, nc, nd] = map NodeId [0..3]
    configGen   = RelayNodeConfig processingDelay generationPattern
    configRelay = RelayNodeConfig processingDelay NoPacketGeneration
    processingDelay = const 0.1 -- 100 ms

    tracer :: Tracer (IOSim s) RelaySimEvent
    tracer = simTracer

    nodeTracer :: NodeId -> Tracer (IOSim s) (RelayNodeEvent TestBlock)
    nodeTracer n =
      contramap (RelaySimEventNode . LabelNode n) tracer

    linkTracer :: NodeId -> NodeId
               -> Tracer (IOSim s)
                         (LabelTcpDir (TcpEvent TestBlockRelayMessage))
    linkTracer nfrom nto =
      contramap (RelaySimEventTcp . labelDirToLabelLink nfrom nto) tracer

