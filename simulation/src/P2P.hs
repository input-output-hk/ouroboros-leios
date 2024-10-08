{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}

module P2P where

import Control.Monad (when)
import Control.Monad.Class.MonadTime.SI (DiffTime)
import Control.Monad.ST (ST)
import Data.Array.ST as Array (
  Ix (range),
  MArray (newArray),
  STUArray,
  readArray,
  runSTUArray,
  writeArray,
 )
import Data.Array.Unboxed as Array (IArray (bounds), UArray, (!))
import Data.Graph as Graph (Edge, Graph, Vertex, buildG, edges)
import qualified Data.KdMap.Static as KdMap
import Data.List (mapAccumL, sort, unfoldr)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import System.Random (StdGen)
import qualified System.Random as Random

import SimTypes (NodeId (..), Point (..), WorldShape (..))

data P2PTopography = P2PTopography
  { p2pNodes :: !(Map NodeId Point)
  , p2pLinks :: !(Map (NodeId, NodeId) Latency)
  , p2pWorldShape :: !WorldShape
  }
  deriving (Show)

type Latency =
  -- | Double rather than DiffTime for efficiency
  Double

data P2PTopographyCharacteristics = P2PTopographyCharacteristics
  { p2pWorldShape :: !WorldShape
  -- ^ Size of the world (in seconds): (Circumference, pole-to-pole)
  , -- \^ Number of nodes, e.g. 100, 1000, 10,000
    p2pNumNodes :: Int
  -- ^ Per-node upstream links picked as close peers, e.g. 5 of 10 total
  , p2pNodeLinksClose :: Int
  -- ^ Per-node upstream links picked as random peers, e.g. 5 of 10 total
  , p2pNodeLinksRandom :: Int
  }
  deriving (Show)

-- | Strategy for creating an arbitrary P2P network:
--
-- * The world is a 2-d rectangle, with the topologoy of a cylinder: connected
--   around the middle but not over the poles. This means the shortest link between
--   two nodes can cros the "date line".
-- * Scatter nodes randomly on the rectangle
-- * All links will be directed
-- * For a given uniform in-degree (e.g. 10-20) pick upstream peers by the
--   "close + random" strategy, e.g. 50%:50%, or 40%:60%
-- * For close peers, pick the first N peers by min distance.
-- * For random peers, pick randomly (perhaps avoiding ones already picked, or self)
-- * The latency of each link will be chosen based on the shortest distance
--   between the nodes: connecting over the "date line" if necessary.
genArbitraryP2PTopography ::
  P2PTopographyCharacteristics ->
  StdGen ->
  P2PTopography
genArbitraryP2PTopography
  P2PTopographyCharacteristics
    { p2pWorldShape =
      p2pWorldShape@WorldShape
        { worldDimensions = (widthSeconds, heightSeconds)
        , worldIsCylinder
        }
    , p2pNumNodes
    , p2pNodeLinksClose
    , p2pNodeLinksRandom
    }
  rng0 =
    P2PTopography
      { p2pNodes = nodePositions
      , p2pLinks = nodeLinks
      , p2pWorldShape
      }
   where
    nodes :: [NodeId]
    nodes = [NodeId n | n <- [0 .. p2pNumNodes - 1]]

    (rngNodes, rngLinks) = Random.split rng0

    nodePositions :: Map NodeId Point
    nodePositions =
      Map.fromList $ snd $ mapAccumL genNodePos rngNodes nodes
     where
      genNodePos :: StdGen -> NodeId -> (StdGen, (NodeId, Point))
      genNodePos rng nodeid =
        (rng'', (nodeid, Point x y))
       where
        x, y :: Double
        (x, !rng') = Random.uniformR (0, widthSeconds) rng
        (y, !rng'') = Random.uniformR (0, heightSeconds) rng'

    nodeLinks :: Map (NodeId, NodeId) Latency
    nodeLinks =
      Map.fromList
        [ ((nid, nid'), latency)
        | (nid, rng) <- zip nodes (unfoldr (Just . Random.split) rngLinks)
        , let p = nodePositions Map.! nid
        , nid' <-
            pickNodeLinksClose p
              ++ pickNodeLinksRandom nid rng
        , let p' = nodePositions Map.! nid'
              !latency = linkLatency p p'
        ]

    pickNodeLinksClose :: Point -> [NodeId]
    pickNodeLinksClose =
      map snd
        . KdMap.kNearest nodesKdMap p2pNodeLinksClose

    -- For efficiency in finding the K nearest neighbours, we use a K-D map
    -- of all the nodes, and then do queries in that.
    nodesKdMap :: KdMap.KdMap Latency Point NodeId
    nodesKdMap =
      KdMap.buildWithDist
        (\(Point x y) -> [x, y])
        linkLatencySquared
        [(p, n) | (n, p) <- Map.toList nodePositions]

    pickNodeLinksRandom :: NodeId -> StdGen -> [NodeId]
    pickNodeLinksRandom nid rng =
      take
        p2pNodeLinksRandom
        [ NodeId nid'
        | nid' <- Random.randomRs (0, p2pNumNodes - 1) rng
        , nid /= NodeId nid'
        ]

    linkLatency :: Point -> Point -> Latency
    linkLatency p1 p2 =
      sqrt (linkLatencySquared p1 p2)

    linkLatencySquared :: Point -> Point -> Latency
    linkLatencySquared p1 p2
      | worldIsCylinder = min d2 d2'
      | otherwise = d2
     where
      (d2, d2') = linkPathLatenciesSquared widthSeconds p1 p2

-- | The latencies of the two different paths between two points: direct
-- and the other way around the world.
linkPathLatenciesSquared :: Latency -> Point -> Point -> (Latency, Latency)
linkPathLatenciesSquared widthSeconds (Point x1 y1) (Point x2 y2) =
  (d2, d2')
 where
  d2 =
    pointToPointLatencySquared
      (Point x1 y1)
      (Point x2 y2)
  d2'
    | x1 <= x2 =
        pointToPointLatencySquared
          (Point (x1 + widthSeconds) y1)
          (Point x2 y2)
    | otherwise =
        pointToPointLatencySquared
          (Point x1 y1)
          (Point (x2 + widthSeconds) y2)

-- | The square of the distance between two points.
-- Why squared? For efficiency, avoiding a square root.
pointToPointLatencySquared :: Point -> Point -> Latency
pointToPointLatencySquared (Point x1 y1) (Point x2 y2) =
  dx * dx + dy * dy
 where
  dx = x1 - x2
  dy = y1 - y2

exampleTopographyCharacteristics1 :: P2PTopographyCharacteristics
exampleTopographyCharacteristics1 =
  P2PTopographyCharacteristics
    { p2pWorldShape =
        WorldShape
          { worldDimensions = (0.600, 0.300)
          , worldIsCylinder = True
          }
    , p2pNumNodes = 50
    , p2pNodeLinksClose = 5
    , p2pNodeLinksRandom = 5
    }

data P2PIdealDiffusionTimes
  = P2PIdealDiffusionTimes !Graph !(UArray (Vertex, Vertex) Double)

-- | The timeseries of the ideal\/perfect diffusion times from the given node
-- to all other nodes.
p2pGraphIdealDiffusionTimesFromNode ::
  P2PIdealDiffusionTimes ->
  -- | From this node to all other nodes
  NodeId ->
  [DiffTime]
p2pGraphIdealDiffusionTimesFromNode
  (P2PIdealDiffusionTimes g latencies)
  (NodeId nid) =
    sort
      [ realToFrac (latencies ! (nid, nid'))
      | nid' <- range (bounds g)
      ]

-- | Compute the ideal\/perfect diffusion times between all nodes.
--
-- This depends on the p2p graph and on the processing and communication times.
-- The communication time must be provided as a function from the one-way link
-- latency. For example, a protocol that involved 3 one-way ballistic message
-- exchanges (for hypothetical zero-sized messages) would be three times the
-- latency. This function should also take account of serialisation and
-- processing delays if approproate.
p2pGraphIdealDiffusionTimes ::
  P2PTopography ->
  -- | Per node processing time
  (NodeId -> DiffTime) ->
  -- | Communication latency between nodes,
  -- given the link one-way link latency
  (NodeId -> NodeId -> DiffTime -> DiffTime) ->
  P2PIdealDiffusionTimes
p2pGraphIdealDiffusionTimes
  P2PTopography{p2pNodes, p2pLinks}
  processingDelay
  communicationDelay =
    P2PIdealDiffusionTimes p2pGraph $
      allPairsMinWeights
        p2pGraph
        ( \(a, b) ->
            let linkLatency :: Latency
                linkLatency = p2pLinks Map.! (NodeId a, NodeId b)
                msgLatency :: DiffTime
                msgLatency =
                  communicationDelay
                    (NodeId a)
                    (NodeId b)
                    (realToFrac linkLatency)
             in realToFrac msgLatency
        )
        (realToFrac . processingDelay . NodeId)
   where
    p2pGraph :: Graph
    p2pGraph =
      Graph.buildG
        (0, Map.size p2pNodes - 1)
        [(a, b) | (NodeId a, NodeId b) <- Map.keys p2pLinks]

allPairsMinWeights ::
  Graph ->
  (Edge -> Double) ->
  (Vertex -> Double) ->
  UArray (Vertex, Vertex) Double
allPairsMinWeights g edgeWeight vertexWeight =
  runSTUArray floydWarshall
 where
  floydWarshall :: ST s (STUArray s (Int, Int) Double)
  floydWarshall = do
    let (_, n) = bounds g
        infinity = 1 / 0 :: Double
    arr <- newArray ((0, 0), (n, n)) infinity
    sequence_ [writeArray arr e (edgeWeight e) | e <- edges g]
    sequence_ [writeArray arr (v, v) 0 | v <- [0 .. n]]
    sequence_
      [ do
        w_ik <- readArray arr (i, k)
        w_kj <- readArray arr (k, j)
        w_ij <- readArray arr (i, j)
        let !w_ikj = w_ik + w_kj + vertexWeight k
        when (w_ij > w_ikj) $
          writeArray arr (i, j) w_ikj
      | k <- [0 .. n]
      , i <- [0 .. n]
      , j <- [0 .. n]
      ]
    return arr
