{-# LANGUAGE FlexibleInstances #-}

module PraosProtocol.SimBlockFetch where

import Chan (Chan)
import Chan.Driver (ProtocolMessage)
import Chan.TCP
import Control.Monad
import Control.Monad.Class.MonadAsync (
  MonadAsync (..),
  mapConcurrently_,
 )
import Control.Monad.IOSim as IOSim (IOSim, runSimTrace)
import Control.Tracer as Tracer (
  Contravariant (contramap),
  Tracer (..),
  traceWith,
 )
import qualified Data.ByteString as BS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import ModelTCP (mkTcpConnProps)
import PraosProtocol.BlockFetch
import PraosProtocol.Common hiding (Point)
import STMCompat
import SimTCPLinks
import SimTypes

type BlockFetchTrace = [(Time, BlockFetchEvent)]

data BlockFetchEvent
  = -- | Declare the nodes and links
    BlockFetchEventSetup
      !World
      !(Map NodeId Point) -- nodes and locations
      !(Set (NodeId, NodeId)) -- links between nodes
  | -- | An event at a node
    BlockFetchEventNode (LabelNode BlockFetchNodeEvent)
  | -- | An event on a tcp link between two nodes
    BlockFetchEventTcp (LabelLink (TcpEvent (ProtocolMessage (BlockFetchState BlockBody))))
  deriving (Show)

data BlockFetchNodeEvent = BlockFetchNodeEvent
  deriving (Show)

exampleTrace1 :: BlockFetchTrace
exampleTrace1 = traceRelayLink1 $ mkTcpConnProps 0.1 1000000

traceRelayLink1 ::
  TcpConnProps ->
  --- PacketGenerationPattern ->
  BlockFetchTrace
traceRelayLink1 tcpprops =
  selectTimedEvents $
    runSimTrace $ do
      traceWith tracer $
        BlockFetchEventSetup
          World
            { worldDimensions = (500, 500)
            , worldShape = Rectangle
            }
          ( Map.fromList
              [ (NodeId 0, Point 50 100)
              , (NodeId 1, Point 450 100)
              ]
          )
          ( Set.fromList
              [(NodeId 0, NodeId 1), (NodeId 1, NodeId 0)]
          )
      (inChan, outChan) <- newConnectionTCP (linkTracer na nb) tcpprops
      let praosConfig = defaultPraosConfig
      concurrently_
        (nodeA praosConfig outChan)
        (nodeB inChan)
      return ()
 where
  -- Soon-To-Be-Shared Chain
  bchain = mkChainSimple $ [BlockBody (BS.pack [i]) (kilobytes 95) | i <- [0 .. 10]]

  -- Block-Fetch Controller & Consumer
  nodeA :: (MonadAsync m, MonadDelay m, MonadSTM m) => PraosConfig BlockBody -> Chan m (ProtocolMessage (BlockFetchState BlockBody)) -> m ()
  nodeA praosConfig chan = do
    peerChainVar <- newTVarIO (blockHeader <$> bchain)
    (st, peerId) <- newBlockFetchControllerState Genesis >>= addPeer (asReadOnly peerChainVar)
    taskTMVar <- newEmptyTMVarIO
    let queue (_, t) = putTMVar taskTMVar t
    let processingThread = forever $ do
          join $ atomically $ takeTMVar taskTMVar
    (ts, submitFetchedBlock) <- setupValidatorThreads praosConfig st queue
    concurrently_ processingThread $
      concurrently_ (mapConcurrently_ id ts) $
        concurrently_
          ( blockFetchController nullTracer st
          )
          ( runBlockFetchConsumer nullTracer praosConfig chan $
              initBlockFetchConsumerStateForPeerId nullTracer peerId st submitFetchedBlock
          )
  -- Block-Fetch Producer
  nodeB chan = do
    st <- BlockFetchProducerState . asReadOnly <$> newTVarIO (toBlocks bchain)
    runBlockFetchProducer chan st

  (na, nb) = (NodeId 0, NodeId 1)

  nullTracer :: Monad m => Tracer m a
  nullTracer = Tracer $ const $ return ()

  tracer :: Tracer (IOSim s) BlockFetchEvent
  tracer = simTracer

  linkTracer ::
    NodeId ->
    NodeId ->
    Tracer
      (IOSim s)
      (LabelTcpDir (TcpEvent (ProtocolMessage (BlockFetchState BlockBody))))
  linkTracer nfrom nto =
    contramap (BlockFetchEventTcp . labelDirToLabelLink nfrom nto) tracer
