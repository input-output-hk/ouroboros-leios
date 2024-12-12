{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module LeiosProtocol.Short.VizSim where

import ChanDriver
import Control.Exception (assert)
import Data.Coerce (coerce)
import Data.Hashable (hash)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as PQ
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Records
import qualified Graphics.Rendering.Cairo as Cairo
import LeiosProtocol.Common hiding (Point)
import LeiosProtocol.Relay (Message (MsgRespondBodies), RelayMessage, relayMessageLabel)
import LeiosProtocol.Short.Node (BlockEvent (..), LeiosEventBlock (..), LeiosMessage (..), LeiosNodeEvent (..), RelayEBMessage, RelayIBMessage, RelayVoteMessage)
import LeiosProtocol.Short.Sim (LeiosEvent (..), LeiosTrace, exampleTrace1)
import ModelTCP
import Network.TypedProtocol
import P2P (linkPathLatenciesSquared)
import PraosProtocol.Common hiding (Point)
import PraosProtocol.PraosNode (PraosMessage (..))
import qualified PraosProtocol.VizSimPraos as VizSimPraos
import SimTypes
import Viz
import VizSim
import VizSimTCP (
  TcpSimVizConfig (..),
  lineMessageInFlight,
  renderMessagesInFlight,
 )
import VizUtils

example1 :: Visualization
example1 =
  slowmoVisualization 0.5 $
    Viz model $
      LayoutReqSize 500 650 $
        Layout $
          leiosSimVizRender examplesLeiosSimVizConfig
 where
  model = leiosSimVizModel trace
   where
    trace = exampleTrace1

examplesLeiosSimVizConfig :: LeiosVizConfig
examplesLeiosSimVizConfig = LeiosVizConfig{..}
 where
  VizSimPraos.PraosVizConfig{..} = VizSimPraos.examplesPraosSimVizConfig
  praosMessageColor = either chainSyncMessageColor blockFetchMessageColor . coerce
  praosMessageText = either chainSyncMessageText blockFetchMessageText . coerce
  relayIBMessageColor :: RelayIBMessage -> (Double, Double, Double)
  relayIBMessageColor = relayMessageColor $ \(InputBlockId x y) -> (x, y)
  relayEBMessageColor :: RelayEBMessage -> (Double, Double, Double)
  relayEBMessageColor = relayMessageColor $ \(EndorseBlockId x y) -> (x, y)
  relayVoteMessageColor :: RelayVoteMessage -> (Double, Double, Double)
  relayVoteMessageColor = relayMessageColor $ \(VoteId x y) -> (x, y)
  relayIBMessageText :: RelayIBMessage -> Maybe String
  relayIBMessageText = relayMessageText "IB:"
  relayEBMessageText :: RelayEBMessage -> Maybe String
  relayEBMessageText = relayMessageText "EB:"
  relayVoteMessageText :: RelayVoteMessage -> Maybe String
  relayVoteMessageText = relayMessageText "Vote:"
  relayMessageText prefix (ProtocolMessage (SomeMessage msg)) = Just $ prefix ++ relayMessageLabel msg
  relayMessageColor :: (id -> (NodeId, Int)) -> RelayMessage id header body -> (Double, Double, Double)
  relayMessageColor f (ProtocolMessage (SomeMessage msg)) = case msg of
    MsgRespondBodies bodies -> hashToColor . hash $ map (f . fst) bodies
    _otherwise -> (1, 0, 0)

------------------------------------------------------------------------------
-- The vizualisation model
--

-- | The vizualisation data model for the relay simulation
type LeiosSimVizModel =
  SimVizModel
    LeiosEvent
    LeiosSimVizState

-- | The vizualisation state within the data model for the relay simulation
data LeiosSimVizState
  = LeiosSimVizState
  { vizWorldShape :: !WorldShape
  , vizNodePos :: !(Map NodeId Point)
  , vizNodeLinks :: !(Map (NodeId, NodeId) LinkPoints)
  , vizMsgsInTransit ::
      !( Map
          (NodeId, NodeId)
          [ ( LeiosMessage
            , TcpMsgForecast
            , [TcpMsgForecast]
            )
          ]
       )
  , vizNodeTip :: !(Map NodeId FullTip)
  , -- the Buffer and Queue names are legacy from VizSimRelay.
    -- In Praos we consider:
    --  * Queue = seen by blockFetchConsumer and not yet in Buffer
    --  * Buffer = added to blocksVar
    vizMsgsAtNodeQueue :: !(Map NodeId [RankingBlockHeader])
  , vizMsgsAtNodeBuffer :: !(Map NodeId [RankingBlockHeader])
  , vizMsgsAtNodeRecentQueue :: !(Map NodeId RecentRate)
  , vizMsgsAtNodeRecentBuffer :: !(Map NodeId RecentRate)
  , vizMsgsAtNodeTotalQueue :: !(Map NodeId Int)
  , vizMsgsAtNodeTotalBuffer :: !(Map NodeId Int)
  , -- these are `Block`s generated (globally).
    vizNumMsgsGenerated :: !Int
  , vizMsgsDiffusionLatency :: !DiffusionLatencyMap
  , ibMsgs :: !(LeiosSimVizMsgsState InputBlockId InputBlock)
  , ebMsgs :: !(LeiosSimVizMsgsState EndorseBlockId EndorseBlock)
  , voteMsgs :: !(LeiosSimVizMsgsState VoteId VoteMsg)
  , ibsInRBs :: !IBsInRBsState
  }

data LeiosSimVizMsgsState id msg = LeiosSimVizMsgsState
  { msgsAtNodeQueue :: !(Map NodeId [msg])
  , msgsAtNodeBuffer :: !(Map NodeId [msg])
  , msgsAtNodeRecentQueue :: !(Map NodeId RecentRate)
  , msgsAtNodeRecentBuffer :: !(Map NodeId RecentRate)
  , msgsAtNodeTotalQueue :: !(Map NodeId Int)
  , msgsAtNodeTotalBuffer :: !(Map NodeId Int)
  , -- these are `Block`s generated (globally).
    numMsgsGenerated :: !Int
  }

data IBsInRBsState = IBsInRBsState
  { ibsInEBs :: !(Map EndorseBlockId (Set InputBlockId))
  , ebsInRBs :: !(Map RankingBlockId (Set EndorseBlockId))
  }

data IBsInRBsReport = IBsInRBsReport {ibsInRBsNum :: !Int, ibsInEBsNum :: !Int, ebsInRBsNum :: !Int}

totalIBsInRBs :: IBsInRBsState -> IBsInRBsReport
totalIBsInRBs s = IBsInRBsReport{..}
 where
  elemsSet x = Set.unions . Map.elems $ x
  ibsInRBsNum = Set.size $ elemsSet $ Map.restrictKeys s.ibsInEBs ebsInRBsSet
  ebsInRBsSet = elemsSet s.ebsInRBs
  ebsInRBsNum = Set.size ebsInRBsSet
  ibsInEBsNum = Set.size $ elemsSet s.ibsInEBs

-- | The end points where the each link, including the case where the link
-- wraps around on a cylindrical world.
data LinkPoints
  = -- | The link goes directly from the node point to node point, without
    -- wrapping around across the West\/East edge.
    LinkPointsNoWrap {-# UNPACK #-} !Point {-# UNPACK #-} !Point
  | -- The link does cross the West\/East edge. The points provided are the
    -- starting node point, two virtual points outside the world rectangle
    -- indicating where a node following a straight line would be, and the
    -- final node point. So if one draws lines between the two pairs of
    -- points (with appropriate clipping) then it will look like it wraps
    -- around.
    LinkPointsWrap
      {-# UNPACK #-} !Point
      {-# UNPACK #-} !Point
      {-# UNPACK #-} !Point
      {-# UNPACK #-} !Point
  deriving (Show)

type ChainsMap = IntMap (Chain (Block RankingBlockBody))

accumChains :: Time -> LeiosEvent -> ChainsMap -> ChainsMap
accumChains _ (LeiosEventNode (LabelNode nid (PraosNodeEvent (PraosNodeEventNewTip ch)))) = IMap.insert (coerce nid) ch
accumChains _ _ = id

type DiffusionLatencyMap = Map (HeaderHash RankingBlockHeader) (RankingBlockHeader, NodeId, Time, [Time])

accumDiffusionLatency :: Time -> LeiosEvent -> DiffusionLatencyMap -> DiffusionLatencyMap
accumDiffusionLatency now (LeiosEventNode (LabelNode n (PraosNodeEvent e))) = accumDiffusionLatency' now (LabelNode n e)
accumDiffusionLatency _ _ = id
accumDiffusionLatency' :: Time -> LabelNode (PraosNodeEvent RankingBlockBody) -> DiffusionLatencyMap -> DiffusionLatencyMap
accumDiffusionLatency' now (LabelNode nid (PraosNodeEventGenerate blk)) vs =
  assert (not (blockHash blk `Map.member` vs)) $
    Map.insert
      (blockHash blk)
      (blockHeader blk, nid, now, [now])
      vs
accumDiffusionLatency' now (LabelNode _nid (PraosNodeEventEnterState blk)) vs =
  Map.adjust
    ( \(hdr, nid', created, arrivals) ->
        (hdr, nid', created, now : arrivals)
    )
    (blockHash blk)
    vs
accumDiffusionLatency' _ _ vs = vs

-- | Make the vizualisation model for the relay simulation from a simulation
-- trace.
leiosSimVizModel ::
  LeiosTrace ->
  VizModel LeiosSimVizModel
leiosSimVizModel =
  simVizModel
    accumEventVizState
    pruneVisState
    initVizState
 where
  initVizState =
    LeiosSimVizState
      { vizWorldShape = WorldShape (0, 0) False
      , vizNodePos = Map.empty
      , vizNodeLinks = Map.empty
      , vizMsgsInTransit = Map.empty
      , vizNodeTip = Map.empty
      , vizMsgsAtNodeQueue = Map.empty
      , vizMsgsAtNodeBuffer = Map.empty
      , vizMsgsAtNodeRecentQueue = Map.empty
      , vizMsgsAtNodeRecentBuffer = Map.empty
      , vizMsgsAtNodeTotalQueue = Map.empty
      , vizMsgsAtNodeTotalBuffer = Map.empty
      , vizNumMsgsGenerated = 0
      , vizMsgsDiffusionLatency = Map.empty
      , ibMsgs = initMsgs
      , ebMsgs = initMsgs
      , voteMsgs = initMsgs
      , ibsInRBs = IBsInRBsState Map.empty Map.empty
      }

  accumEventVizState ::
    Time ->
    LeiosEvent ->
    LeiosSimVizState ->
    LeiosSimVizState
  accumEventVizState _now (LeiosEventSetup shape nodes links) vs =
    vs
      { vizWorldShape = shape
      , vizNodePos = nodes
      , vizNodeLinks =
          Map.fromSet
            ( \(n1, n2) ->
                linkPoints
                  shape
                  (nodes Map.! n1)
                  (nodes Map.! n2)
            )
            links
      }
  accumEventVizState _now (LeiosEventNode (LabelNode nid (PraosNodeEvent (PraosNodeEventNewTip tip)))) vs =
    vs{vizNodeTip = Map.insert nid (fullTip tip) (vizNodeTip vs)}
  accumEventVizState now (LeiosEventNode (LabelNode nid (LeiosNodeEvent event blk))) vs =
    case blk of
      EventIB x -> vs{ibMsgs = accumLeiosMsgs now nid event x vs.ibMsgs}
      EventEB x ->
        vs
          { ebMsgs = accumLeiosMsgs now nid event x vs.ebMsgs
          , ibsInRBs = case event of
              Generate -> accumIBsInRBs (Right x) vs.ibsInRBs
              _ -> vs.ibsInRBs
          }
      EventVote x -> vs{voteMsgs = accumLeiosMsgs now nid event x vs.voteMsgs}
  accumEventVizState now (LeiosEventNode (LabelNode nid (PraosNodeEvent (PraosNodeEventGenerate blk)))) vs =
    vs
      { vizMsgsAtNodeBuffer =
          Map.insertWith (flip (++)) nid [blockHeader blk] (vizMsgsAtNodeBuffer vs)
      , vizMsgsAtNodeRecentBuffer =
          Map.alter
            (Just . recentAdd now . fromMaybe recentEmpty)
            nid
            (vizMsgsAtNodeRecentBuffer vs)
      , vizMsgsAtNodeTotalBuffer =
          Map.insertWith (+) nid 1 (vizMsgsAtNodeTotalBuffer vs)
      , vizNumMsgsGenerated = vizNumMsgsGenerated vs + 1
      , vizMsgsDiffusionLatency =
          assert (not (blockHash blk `Map.member` vizMsgsDiffusionLatency vs)) $
            Map.insert
              (blockHash blk)
              (blockHeader blk, nid, now, [now])
              (vizMsgsDiffusionLatency vs)
      , ibsInRBs = accumIBsInRBs (Left blk) vs.ibsInRBs
      }
  accumEventVizState now (LeiosEventNode (LabelNode nid (PraosNodeEvent (PraosNodeEventReceived blk)))) vs =
    vs
      { vizMsgsAtNodeQueue =
          Map.insertWith (flip (++)) nid [blockHeader blk] (vizMsgsAtNodeQueue vs)
      , vizMsgsAtNodeRecentQueue =
          Map.alter
            (Just . recentAdd now . fromMaybe recentEmpty)
            nid
            (vizMsgsAtNodeRecentQueue vs)
      , vizMsgsAtNodeTotalQueue =
          Map.insertWith (+) nid 1 (vizMsgsAtNodeTotalQueue vs)
      }
  accumEventVizState now (LeiosEventNode (LabelNode nid (PraosNodeEvent (PraosNodeEventEnterState blk)))) vs =
    vs
      { vizMsgsAtNodeBuffer =
          Map.insertWith (flip (++)) nid [blockHeader blk] (vizMsgsAtNodeBuffer vs)
      , vizMsgsAtNodeQueue =
          Map.adjust
            (filter (\blk' -> blockHash blk' /= blockHash blk))
            nid
            (vizMsgsAtNodeQueue vs)
      , vizMsgsAtNodeRecentBuffer =
          Map.alter
            (Just . recentAdd now . fromMaybe recentEmpty)
            nid
            (vizMsgsAtNodeRecentBuffer vs)
      , vizMsgsAtNodeTotalBuffer =
          Map.insertWith (+) nid 1 (vizMsgsAtNodeTotalBuffer vs)
      , vizMsgsDiffusionLatency =
          Map.adjust
            ( \(hdr, nid', created, arrivals) ->
                (hdr, nid', created, now : arrivals)
            )
            (blockHash blk)
            (vizMsgsDiffusionLatency vs)
      }
  accumEventVizState
    _now
    ( LeiosEventTcp
        ( LabelLink
            nfrom
            nto
            (TcpSendMsg msg msgforecast msgforecasts)
          )
      )
    vs =
      vs
        { vizMsgsInTransit =
            Map.insertWith
              (flip (++))
              (nfrom, nto)
              [(msg, msgforecast, msgforecasts)]
              (vizMsgsInTransit vs)
        }
  accumEventVizState _now (LeiosEventNode (LabelNode _nodeId (LeiosNodeEventCPU _task))) vs = vs
  accumEventVizState
    _now
    ( LeiosEventNode
        (LabelNode _nodeId (PraosNodeEvent (PraosNodeEventCPU _task)))
      )
    vs = vs

  pruneVisState ::
    Time ->
    LeiosSimVizState ->
    LeiosSimVizState
  pruneVisState now vs =
    vs
      { vizMsgsInTransit =
          Map.map
            ( filter
                ( \(_, msgforecast, _) ->
                    now <= msgAcknowledgement msgforecast
                )
            )
            (vizMsgsInTransit vs)
      , vizMsgsAtNodeRecentQueue =
          Map.map (recentPrune secondsAgo30) (vizMsgsAtNodeRecentQueue vs)
      , vizMsgsAtNodeRecentBuffer =
          Map.map (recentPrune secondsAgo30) (vizMsgsAtNodeRecentBuffer vs)
      , vizMsgsDiffusionLatency =
          Map.filter (\(_, _, t, _) -> t >= secondsAgo30) (vizMsgsDiffusionLatency vs)
      , ibMsgs = pruneLeiosMsgsState now vs.ibMsgs
      , ebMsgs = pruneLeiosMsgsState now vs.ebMsgs
      , voteMsgs = pruneLeiosMsgsState now vs.voteMsgs
      }
   where
    secondsAgo30 :: Time
    secondsAgo30 = addTime (-30) now

initMsgs :: LeiosSimVizMsgsState id msg
initMsgs =
  LeiosSimVizMsgsState
    { msgsAtNodeQueue = Map.empty
    , msgsAtNodeBuffer = Map.empty
    , msgsAtNodeRecentQueue = Map.empty
    , msgsAtNodeRecentBuffer = Map.empty
    , msgsAtNodeTotalQueue = Map.empty
    , msgsAtNodeTotalBuffer = Map.empty
    , numMsgsGenerated = 0
    }

accumLeiosMsgs ::
  (Eq id, HasField "id" msg id) =>
  Time ->
  NodeId ->
  BlockEvent ->
  msg ->
  LeiosSimVizMsgsState id msg ->
  LeiosSimVizMsgsState id msg
accumLeiosMsgs now nid Generate blk vs =
  vs
    { msgsAtNodeBuffer =
        Map.insertWith (flip (++)) nid [blk] (msgsAtNodeBuffer vs)
    , msgsAtNodeRecentBuffer =
        Map.alter
          (Just . recentAdd now . fromMaybe recentEmpty)
          nid
          (msgsAtNodeRecentBuffer vs)
    , msgsAtNodeTotalBuffer =
        Map.insertWith (+) nid 1 (msgsAtNodeTotalBuffer vs)
    , numMsgsGenerated = numMsgsGenerated vs + 1
    }
accumLeiosMsgs now nid Received blk vs =
  vs
    { msgsAtNodeQueue =
        Map.insertWith (flip (++)) nid [blk] (msgsAtNodeQueue vs)
    , msgsAtNodeRecentQueue =
        Map.alter
          (Just . recentAdd now . fromMaybe recentEmpty)
          nid
          (msgsAtNodeRecentQueue vs)
    , msgsAtNodeTotalQueue =
        Map.insertWith (+) nid 1 (msgsAtNodeTotalQueue vs)
    }
accumLeiosMsgs now nid EnterState blk vs =
  vs
    { msgsAtNodeBuffer =
        Map.insertWith (flip (++)) nid [blk] (msgsAtNodeBuffer vs)
    , msgsAtNodeQueue =
        Map.adjust
          (filter (\blk' -> blk'.id /= blk.id))
          nid
          (msgsAtNodeQueue vs)
    , msgsAtNodeRecentBuffer =
        Map.alter
          (Just . recentAdd now . fromMaybe recentEmpty)
          nid
          (msgsAtNodeRecentBuffer vs)
    , msgsAtNodeTotalBuffer =
        Map.insertWith (+) nid 1 (msgsAtNodeTotalBuffer vs)
    }

pruneLeiosMsgsState ::
  (Eq id, HasField "id" msg id) =>
  Time ->
  LeiosSimVizMsgsState id msg ->
  LeiosSimVizMsgsState id msg
pruneLeiosMsgsState now vs =
  vs
    { msgsAtNodeRecentQueue =
        Map.map (recentPrune secondsAgo30) (msgsAtNodeRecentQueue vs)
    , msgsAtNodeRecentBuffer =
        Map.map (recentPrune secondsAgo30) (msgsAtNodeRecentBuffer vs)
    }
 where
  secondsAgo30 :: Time
  secondsAgo30 = addTime (-30) now

accumIBsInRBs :: Either RankingBlock EndorseBlock -> IBsInRBsState -> IBsInRBsState
accumIBsInRBs (Left rb) s = s{ebsInRBs = Map.insertWith Set.union (blockHash rb) (Set.fromList $ map fst rb.blockBody.endorseBlocks) s.ebsInRBs}
accumIBsInRBs (Right eb) s = s{ibsInEBs = Map.insertWith Set.union eb.id (Set.fromList eb.inputBlocks) s.ibsInEBs}

-- | The shortest distance between two points, given that the world may be
-- considered to be a cylinder.
--
-- These points are computed in normalised (unit square) coordinates
linkPoints :: WorldShape -> Point -> Point -> LinkPoints
linkPoints
  WorldShape{worldDimensions = (widthSeconds, _), worldIsCylinder}
  p1@(Point x1 y1)
  p2@(Point x2 y2)
    | not worldIsCylinder || d2 < d2' =
        LinkPointsNoWrap (Point x1 y1) (Point x2 y2)
    | x1 <= x2 =
        LinkPointsWrap
          (Point x1 y1)
          (Point (x2 - widthSeconds) y2)
          (Point (x1 + widthSeconds) y1)
          (Point x2 y2)
    | otherwise =
        LinkPointsWrap
          (Point x1 y1)
          (Point (x2 + widthSeconds) y2)
          (Point (x1 - widthSeconds) y1)
          (Point x2 y2)
   where
    (d2, d2') = linkPathLatenciesSquared widthSeconds p1 p2

newtype RecentRate = RecentRate (MinQueue Time)

recentEmpty :: RecentRate
recentEmpty = RecentRate PQ.empty

recentRate :: RecentRate -> Int
recentRate (RecentRate q) = PQ.size q

recentAdd :: Time -> RecentRate -> RecentRate
recentAdd t (RecentRate pq) = RecentRate (PQ.insert t pq)

recentPrune :: Time -> RecentRate -> RecentRate
recentPrune now (RecentRate pq) =
  case PQ.minView pq of
    Just (t, pq')
      | t < now -> recentPrune now (RecentRate pq')
    _ -> RecentRate pq

------------------------------------------------------------------------------
-- The vizualisation rendering
--

data LeiosVizConfig
  = LeiosVizConfig
  { praosMessageColor :: PraosMessage RankingBlockBody -> (Double, Double, Double)
  , praosMessageText :: PraosMessage RankingBlockBody -> Maybe String
  , relayIBMessageColor :: RelayIBMessage -> (Double, Double, Double)
  , relayIBMessageText :: RelayIBMessage -> Maybe String
  , relayEBMessageColor :: RelayEBMessage -> (Double, Double, Double)
  , relayEBMessageText :: RelayEBMessage -> Maybe String
  , relayVoteMessageColor :: RelayVoteMessage -> (Double, Double, Double)
  , relayVoteMessageText :: RelayVoteMessage -> Maybe String
  }

leiosMessageColor :: LeiosVizConfig -> LeiosMessage -> (Double, Double, Double)
leiosMessageColor LeiosVizConfig{..} msg =
  case msg of
    RelayIB x -> relayIBMessageColor x
    RelayEB x -> relayEBMessageColor x
    RelayVote x -> relayVoteMessageColor x
    PraosMsg x -> praosMessageColor x

leiosMessageText :: LeiosVizConfig -> LeiosMessage -> Maybe String
leiosMessageText LeiosVizConfig{..} msg =
  case msg of
    RelayIB x -> relayIBMessageText x
    RelayEB x -> relayEBMessageText x
    RelayVote x -> relayVoteMessageText x
    PraosMsg x -> praosMessageText x

leiosSimVizRender ::
  LeiosVizConfig ->
  VizRender LeiosSimVizModel
leiosSimVizRender vizConfig =
  VizRender
    { renderReqSize = (500, 500)
    , renderChanged = \_t _fn _m -> True
    , renderModel = \t _fn m sz -> leiosSimVizRenderModel vizConfig t m sz
    }

leiosSimVizRenderModel ::
  LeiosVizConfig ->
  Time ->
  SimVizModel event LeiosSimVizState ->
  (Double, Double) ->
  Cairo.Render ()
leiosSimVizRenderModel
  cfg
  now
  ( SimVizModel
      _events
      LeiosSimVizState
        { vizWorldShape = WorldShape{worldDimensions}
        , vizNodePos
        , vizNodeTip
        , vizNodeLinks
        , vizMsgsInTransit
        , ibMsgs
        }
    )
  screenSize = do
    renderLinks
    renderMessagesAtNodes ibMsgs
    renderNodes
   where
    renderNodes = do
      Cairo.save
      Cairo.setLineWidth 3
      sequence_
        [ do
          Cairo.arc x y 25 0 (pi * 2)
          Cairo.setSourceRGB r b g
          Cairo.fillPreserve
          Cairo.setSourceRGB 0 0 0
          Cairo.stroke
        | (node, pos) <- Map.toList vizNodePos
        , let (Point x y) = simPointToPixel worldDimensions screenSize pos
        , let (r, b, g) = case Map.lookup node vizNodeTip of
                Just (FullTip hdr) -> blockHeaderColorAsBody hdr
                _ -> (0.7, 0.7, 0.7)
        ]
      Cairo.restore

    renderLinks = do
      Cairo.save
      Cairo.setLineCap Cairo.LineCapButt
      Cairo.setLineWidth 3
      sequence_
        [ do
          Cairo.save
          renderPathRoundedRect fromPos toPos 20
          Cairo.setSourceRGB 0.9 0.9 0.9
          Cairo.fillPreserve
          Cairo.clip
          Cairo.newPath
          -- draw all the messages within the clipping region of the link
          renderMessagesInFlight
            ( TcpSimVizConfig $ leiosMessageColor cfg
            )
            now
            fromPos
            toPos
            msgs
          Cairo.restore
          -- the draw the link border on top (without clipping)
          renderPathRoundedRect fromPos toPos 20
          Cairo.setSourceRGB 0 0 0
          Cairo.stroke
        | (fromPos, toPos, msgs) <- linksAndMsgs
        ]
      -- draw the message labels on top of the links
      sequence_
        [ renderMessageLabelsInFlight fromPos toPos msgs
        | (fromPos, toPos, msgs) <- linksAndMsgs
        ]
      Cairo.restore
     where
      linksAndMsgs =
        [ (fromPos, toPos, msgs)
        | (fromNode, toNode) <- Map.keys vizNodeLinks
        , let (fromPos, toPos) =
                translateLineNormal
                  displace
                  ( simPointToPixel worldDimensions screenSize (vizNodePos Map.! fromNode)
                  , simPointToPixel worldDimensions screenSize (vizNodePos Map.! toNode)
                  )
              -- For links in both directions, we need to displace them
              -- so they don't overlap each other, but for unidirectional
              -- links we can draw it centrally.
              displace
                | Map.notMember (toNode, fromNode) vizNodeLinks = 0
                | otherwise = -10

              msgs =
                Map.findWithDefault
                  []
                  (fromNode, toNode)
                  vizMsgsInTransit
        ]

    renderMessageLabelsInFlight fromPos toPos msgs = do
      Cairo.save
      Cairo.setSourceRGB 0.5 0.5 0.5
      Cairo.setFontSize 10
      Cairo.setLineWidth 0.6
      -- draw lines from labels to messages
      sequence_
        [ do
          withPoint Cairo.moveTo (labelsOrigin `addP` Vector 0 (n * 10))
          withPoint Cairo.lineTo msgTrailingEdge
        | ((_msgLabel, msgforecast), n) <- zip msgLabels [0 ..]
        , let (msgTrailingEdge, _msgLeadingEdge) =
                lineMessageInFlight now fromPos toPos msgforecast
        ]
      Cairo.stroke
      -- draw the labels themselves
      Cairo.setSourceRGB 0 0 0
      sequence_
        [ do
          withPoint Cairo.moveTo (labelsOrigin `addP` Vector 0 (n * 10))
          Cairo.showText msgLabel
          Cairo.newPath
        | ((msgLabel, _), n) <- zip msgLabels [0 ..]
        ]
      Cairo.restore
     where
      labelsOrigin = midpointP fromPos toPos `addP` labelsOffset
      labelsOffset = scaleV (-50) $ unitV $ normalV $ vector fromPos toPos
      msgLabels =
        [ (msgLabel, msgforecast)
        | (msg, msgforecast, _) <- msgs
        , now <= msgRecvTrailingEdge msgforecast
        , Just msgLabel <- [leiosMessageText cfg msg]
        ]

    renderMessagesAtNodes LeiosSimVizMsgsState{..} = do
      Cairo.save
      sequence_
        [ do
          Cairo.setSourceRGB r g b
          Cairo.arc (x - 10) y' 10 0 (2 * pi)
          Cairo.fillPreserve
          Cairo.setSourceRGB 0 0 0
          Cairo.setLineWidth 1
          Cairo.stroke
          case nodeMessageText msg of
            Nothing -> return ()
            Just txt -> do
              Cairo.moveTo (x - 32) (y' + 5)
              Cairo.showText txt
              Cairo.newPath
        | (node, msgs) <- Map.toList msgsAtNodeQueue
        , (n, msg) <- zip [1 ..] msgs
        , let (Point x y) =
                simPointToPixel
                  worldDimensions
                  screenSize
                  (vizNodePos Map.! node)
              y' = y + 16 + 20 * n
              (r, g, b) = nodeMessageColor msg
        ]
      sequence_
        [ do
          Cairo.setSourceRGB r g b
          Cairo.arc (x + 10) y' 10 0 (2 * pi)
          Cairo.fillPreserve
          Cairo.setSourceRGB 0 0 0
          Cairo.setLineWidth 1
          Cairo.stroke
          case nodeMessageText msg of
            Nothing -> return ()
            Just txt -> do
              Cairo.moveTo (x + 22) (y' + 5)
              Cairo.showText txt
              Cairo.newPath
        | (node, msgs) <- Map.toList msgsAtNodeBuffer
        , (n, msg) <- zip [1 ..] msgs
        , let (Point x y) =
                simPointToPixel
                  worldDimensions
                  screenSize
                  (vizNodePos Map.! node)
              y' = y + 16 + 20 * n
              (r, g, b) = nodeMessageColor msg
        ]
      Cairo.restore
     where
      nodeMessageText msg = Just $ show $ (\(InputBlockId (NodeId x) y) -> (x, y)) $ msg.id
      nodeMessageColor msg = hashToColor $ hash msg.id
