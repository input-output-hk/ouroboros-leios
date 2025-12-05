{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

module P2P where

import Control.Applicative ((<|>))
import Control.Exception (assert)
import Control.Monad (when)
import Control.Monad.ST (ST)
import Data.Aeson.Types (FromJSON (..), FromJSONKey, KeyValue ((.=)), ToJSON (..), ToJSONKey, defaultOptions, genericToEncoding, object, withObject, (.!=), (.:?))
import Data.Array.ST as Array (
  Ix (range),
  MArray (newArray),
  STUArray,
  readArray,
  runSTUArray,
  writeArray,
 )
import Data.Array.Unboxed as Array (IArray (bounds), UArray, amap, (!))
import Data.Default (Default (..))
import Data.Graph as Graph (Edge, Graph, Vertex, buildG, edges)
import qualified Data.KdMap.Static as KdMap
import Data.List (mapAccumL, sortOn, unfoldr)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import SimTypes (NodeId (..), Point (..), World (..), WorldShape (..))
import qualified System.Random as Random
import TimeCompat

data Link' a = Link {downstream :: !a, upstream :: !a}
  deriving (Eq, Ord, Show, Generic)
type Link = Link' NodeId

pattern (:<-) :: a -> a -> Link' a
pattern (:<-) d u = Link{downstream = d, upstream = u}
{-# COMPLETE (:<-) #-}

data P2PTopography = P2PTopography
  { p2pNodes :: !(Map NodeId Point)
  , p2pLinks :: !(Map Link Latency)
  , p2pWorld :: !World
  }
  deriving (Eq, Show, Generic)

instance ToJSON a => ToJSON (Link' a) where
  toJSON (Link a b) = toJSON (a, b)
  toEncoding (Link a b) = toEncoding (a, b)

instance FromJSON a => FromJSON (Link' a) where
  parseJSON = (fmap . uncurry) Link . parseJSON

instance ToJSON a => ToJSONKey (Link' a)
instance FromJSON a => FromJSONKey (Link' a)

instance ToJSON P2PTopography where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON P2PTopography

-- | Communication over links is bidirectional, so it's useful to look
-- up link information without knowing which end is upstream.
(!!!) :: (Ord k, HasCallStack) => Map (Link' k) a -> (k, k) -> a
(!!!) m (nid, nid') =
  fromMaybe undefined $
    Map.lookup (Link nid nid') m <|> Map.lookup (Link nid' nid) m

traverseLinks :: (Ord k, Monad m) => Map.Map (Link' k) t -> (k -> k -> t -> m (c, c)) -> m (Link' (Map.Map k [c]))
traverseLinks p2pLinks newConn = do
  tcplinks <-
    sequence
      [ do
          (aChan, bChan) <- newConn na nb info
          return ((na :<- nb), (aChan :<- bChan))
      | ((na :<- nb), info) <- Map.toList p2pLinks
      ]
  let chansToUpstream =
        Map.fromListWith
          (++)
          [ (down, [downEnd])
          | (down :<- _, (downEnd :<- _)) <- tcplinks
          ]
      chansToDownstream =
        Map.fromListWith
          (++)
          [ (up, [upEnd])
          | (_ :<- up, (_ :<- upEnd)) <- tcplinks
          ]
  return (chansToDownstream :<- chansToUpstream)

-- | Latency in /seconds/.
--
--   This uses a `Double` rather than a `DiffTime` for compatibility with Cairo.
type Latency = Double

data P2PTopographyCharacteristics = P2PTopographyCharacteristics
  { p2pWorld :: !World
  -- ^ Size of the world (in seconds): (Circumference, pole-to-pole)
  , -- \^ Number of nodes, e.g. 100, 1000, 10,000

    p2pNumNodes :: Int
  -- ^ Per-node upstream links picked as close peers, e.g. 5 of 10 total
  , p2pNodeLinksClose :: Int
  -- ^ Per-node upstream links picked as random peers, e.g. 5 of 10 total
  , p2pNodeLinksRandom :: Int
  }
  deriving (Eq, Show, Generic)

instance Default P2PTopographyCharacteristics where
  def =
    P2PTopographyCharacteristics
      { p2pWorld = def
      , p2pNumNodes = 100
      , p2pNodeLinksClose = 5
      , p2pNodeLinksRandom = 5
      }

instance ToJSON P2PTopographyCharacteristics where
  toJSON P2PTopographyCharacteristics{..} =
    object
      [ "world" .= p2pWorld
      , "num_nodes" .= p2pNumNodes
      , "num_links_close" .= p2pNodeLinksClose
      , "num_links_random" .= p2pNodeLinksRandom
      ]

instance FromJSON P2PTopographyCharacteristics where
  parseJSON = withObject "P2PTopographyCharacteristics" $ \o -> do
    p2pWorld <- o .:? "world" .!= def
    p2pNumNodes <- o .:? "num_nodes" .!= 100
    p2pNodeLinksClose <- o .:? "num_links_close" .!= 5
    p2pNodeLinksRandom <- o .:? "num_links_random" .!= 5
    pure P2PTopographyCharacteristics{..}

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
  forall g.
  (HasCallStack, Random.RandomGen g) =>
  P2PTopographyCharacteristics ->
  g ->
  P2PTopography
genArbitraryP2PTopography
  P2PTopographyCharacteristics
    { p2pWorld =
      p2pWorld@World
        { worldDimensions = (widthSeconds, heightSeconds)
        , worldShape
        }
    , p2pNumNodes
    , p2pNodeLinksClose
    , p2pNodeLinksRandom
    }
  rng0 =
    P2PTopography
      { p2pNodes = nodePositions
      , p2pLinks = nodeLinks
      , p2pWorld
      }
   where
    nodes :: [NodeId]
    nodes = [NodeId n | n <- [0 .. p2pNumNodes - 1]]

    (rngNodes, rngLinks) = Random.split rng0

    nodePositions :: Map NodeId Point
    nodePositions =
      Map.fromList $ snd $ mapAccumL genNodePos rngNodes nodes
     where
      genNodePos :: g -> NodeId -> (g, (NodeId, Point))
      genNodePos rng nodeid =
        (rng'', (nodeid, Point x y))
       where
        x, y :: Double
        (x, !rng') = Random.uniformR (0, widthSeconds) rng
        (y, !rng'') = Random.uniformR (0, heightSeconds) rng'

    nodeLinks :: Map Link Latency
    nodeLinks =
      Map.fromList
        [ ((nid :<- nid'), latency)
        | (nid, rng) <- zip nodes (unfoldr (Just . Random.split) rngLinks)
        , let p = nodePositions Map.! nid
        , nid' <-
            pickNodeLinksClose nid p
              ++ pickNodeLinksRandom nid rng
        , let p' = nodePositions Map.! nid'
              !latency = linkLatency p p'
        ]

    pickNodeLinksClose :: NodeId -> Point -> [NodeId]
    pickNodeLinksClose nid p =
      case map snd $ KdMap.kNearest nodesKdMap (p2pNodeLinksClose + 1) p of
        (nid' : nids) -> assert (nid == nid') nids
        [] -> assert False []

    -- For efficiency in finding the K nearest neighbours, we use a K-D map
    -- of all the nodes, and then do queries in that.
    nodesKdMap :: KdMap.KdMap Latency Point NodeId
    nodesKdMap =
      KdMap.buildWithDist
        (\(Point x y) -> [x, y])
        linkLatencySquared
        [(p, n) | (n, p) <- Map.toList nodePositions]

    pickNodeLinksRandom :: NodeId -> g -> [NodeId]
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
      | worldShape == Cylinder = min d2 d2'
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
    { p2pWorld =
        World
          { worldDimensions = (0.600, 0.300)
          , worldShape = Cylinder
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
p2pGraphIdealDiffusionTimesFromNode times nid =
  map snd $ p2pGraphIdealDiffusionTimesFromNode' times nid

p2pGraphIdealDiffusionTimesFromNode' ::
  P2PIdealDiffusionTimes ->
  -- | From this node to all other nodes
  NodeId ->
  [(NodeId, DiffTime)]
p2pGraphIdealDiffusionTimesFromNode'
  (P2PIdealDiffusionTimes g latencies)
  (NodeId nid) =
    sortOn
      snd
      [ (NodeId nid', secondsToDiffTime (latencies ! (nid, nid')))
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
  -- | Generation time
  DiffTime ->
  -- | Processing time
  DiffTime ->
  -- | Communication latency between nodes,
  -- given the link one-way link latency
  (NodeId -> NodeId -> DiffTime -> DiffTime) ->
  P2PIdealDiffusionTimes
p2pGraphIdealDiffusionTimes
  P2PTopography{p2pNodes, p2pLinks}
  generationDelay
  processingDelay
  communicationDelay =
    P2PIdealDiffusionTimes p2pGraph $
      amap (+ realToFrac generationDelay) $
        allPairsMinWeights
          p2pGraph
          ( \(a, b) ->
              let linkLatency :: Latency
                  linkLatency = p2pLinks !!! (NodeId a, NodeId b)
                  msgLatency :: DiffTime
                  msgLatency =
                    communicationDelay
                      (NodeId a)
                      (NodeId b)
                      (secondsToDiffTime linkLatency)
               in realToFrac msgLatency + realToFrac processingDelay
          )
          (const 0)
   where
    p2pGraph :: Graph
    p2pGraph =
      Graph.buildG
        (0, Map.size p2pNodes - 1)
        [(a, b) | (NodeId a :<- NodeId b) <- Map.keys p2pLinks]

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
