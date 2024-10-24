{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module PraosProtocol.VizSimPraos where

import ChanDriver
import Data.Coerce (coerce)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as PQ
import qualified Graphics.Rendering.Cairo as Cairo
import ModelTCP
import Network.TypedProtocol
import P2P (linkPathLatenciesSquared)
import PraosProtocol.BlockFetch (BlockFetchMessage, Message (MsgBlock), blockFetchMessageLabel)
import PraosProtocol.ChainSync (ChainSyncMessage, Message (..), chainSyncMessageLabel)
import PraosProtocol.Common hiding (Point)
import PraosProtocol.PraosNode (PraosMessage (..))
import PraosProtocol.SimPraos (PraosEvent (..), PraosTrace, exampleTrace1)
import SimTypes
import Viz
import VizSim
import VizSimTCP (
  TcpSimVizConfig (..),
  lineMessageInFlight,
  renderMessagesInFlight,
 )
import VizUtils

example1 :: Vizualisation
example1 =
  slowmoVizualisation 0.1 $
    Viz model $
      LayoutReqSize 500 650 $
        Layout $
          praosSimVizRender examplesPraosSimVizConfig
 where
  model = praosSimVizModel trace
   where
    trace = exampleTrace1

examplesPraosSimVizConfig :: PraosVizConfig
examplesPraosSimVizConfig = PraosVizConfig{..}
 where
  chainSyncMessageColor ::
    ChainSyncMessage ->
    (Double, Double, Double)
  chainSyncMessageColor (ProtocolMessage (SomeMessage (MsgRollForward_StCanAwait blk _))) = blockHeaderColor blk
  chainSyncMessageColor (ProtocolMessage (SomeMessage (MsgRollForward_StMustReply blk _))) = blockHeaderColor blk
  chainSyncMessageColor _ = (1, 0, 0)

  chainSyncMessageText ::
    ChainSyncMessage ->
    Maybe String
  chainSyncMessageText (ProtocolMessage (SomeMessage msg)) = Just $ chainSyncMessageLabel msg

  blockFetchMessageColor ::
    BlockFetchMessage ->
    (Double, Double, Double)
  blockFetchMessageColor (ProtocolMessage (SomeMessage msg)) = case msg of
    MsgBlock blk -> blockBodyColor blk
    _otherwise -> (1, 0, 0)

  blockFetchMessageText ::
    BlockFetchMessage ->
    Maybe String
  blockFetchMessageText (ProtocolMessage (SomeMessage msg)) = Just $ blockFetchMessageLabel msg

------------------------------------------------------------------------------
-- The vizualisation model
--

-- | The vizualisation data model for the relay simulation
type PraosSimVizModel =
  SimVizModel
    PraosEvent
    PraosSimVizState

-- | The vizualisation state within the data model for the relay simulation
data PraosSimVizState
  = PraosSimVizState
  { vizWorldShape :: !WorldShape
  , vizNodePos :: !(Map NodeId Point)
  , vizNodeLinks :: !(Map (NodeId, NodeId) LinkPoints)
  , vizMsgsInTransit ::
      !( Map
          (NodeId, NodeId)
          [ ( PraosMessage
            , TcpMsgForecast
            , [TcpMsgForecast]
            )
          ]
       )
  , vizMsgsAtNodeQueue :: !(Map NodeId [BlockHeader])
  , vizMsgsAtNodeBuffer :: !(Map NodeId [BlockHeader])
  , vizMsgsAtNodeRecentQueue :: !(Map NodeId RecentRate)
  , vizMsgsAtNodeRecentBuffer :: !(Map NodeId RecentRate)
  , vizMsgsAtNodeTotalQueue :: !(Map NodeId Int)
  , vizMsgsAtNodeTotalBuffer :: !(Map NodeId Int)
  , vizNumMsgsGenerated :: !Int
  , vizMsgsDiffusionLatency :: !(Map (HeaderHash BlockHeader) (BlockHeader, NodeId, Time, [Time]))
  }

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

-- | Make the vizualisation model for the relay simulation from a simulation
-- trace.
praosSimVizModel ::
  PraosTrace ->
  VizModel PraosSimVizModel
praosSimVizModel =
  simVizModel
    accumEventVizState
    pruneVisState
    initVizState
 where
  initVizState =
    PraosSimVizState
      { vizWorldShape = WorldShape (0, 0) False
      , vizNodePos = Map.empty
      , vizNodeLinks = Map.empty
      , vizMsgsInTransit = Map.empty
      , vizMsgsAtNodeQueue = Map.empty
      , vizMsgsAtNodeBuffer = Map.empty
      , vizMsgsAtNodeRecentQueue = Map.empty
      , vizMsgsAtNodeRecentBuffer = Map.empty
      , vizMsgsAtNodeTotalQueue = Map.empty
      , vizMsgsAtNodeTotalBuffer = Map.empty
      , vizNumMsgsGenerated = 0
      , vizMsgsDiffusionLatency = Map.empty
      }

  accumEventVizState ::
    Time ->
    PraosEvent ->
    PraosSimVizState ->
    PraosSimVizState
  accumEventVizState _now (PraosEventSetup shape nodes links) vs =
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
  accumEventVizState
    _now
    ( PraosEventTcp
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

  pruneVisState ::
    Time ->
    PraosSimVizState ->
    PraosSimVizState
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
          Map.map (recentPrune secondsAgo1) (vizMsgsAtNodeRecentQueue vs)
      , vizMsgsAtNodeRecentBuffer =
          Map.map (recentPrune secondsAgo1) (vizMsgsAtNodeRecentBuffer vs)
      , vizMsgsDiffusionLatency =
          Map.filter (\(_, _, t, _) -> t >= secondsAgo15) (vizMsgsDiffusionLatency vs)
      }
   where
    secondsAgo1 :: Time
    secondsAgo1 = addTime (-1) now

    secondsAgo15 :: Time
    secondsAgo15 = addTime (-15) now

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

data PraosVizConfig
  = PraosVizConfig
  { chainSyncMessageColor :: ChainSyncMessage -> (Double, Double, Double)
  , chainSyncMessageText :: ChainSyncMessage -> Maybe String
  , blockFetchMessageColor :: BlockFetchMessage -> (Double, Double, Double)
  , blockFetchMessageText :: BlockFetchMessage -> Maybe String
  }

praosSimVizRender ::
  PraosVizConfig ->
  VizRender PraosSimVizModel
praosSimVizRender vizConfig =
  VizRender
    { renderReqSize = (500, 500)
    , renderChanged = \_t _fn _m -> True
    , renderModel = \t _fn m sz -> praosSimVizRenderModel vizConfig t m sz
    }

praosSimVizRenderModel ::
  PraosVizConfig ->
  Time ->
  SimVizModel event PraosSimVizState ->
  (Double, Double) ->
  Cairo.Render ()
praosSimVizRenderModel
  PraosVizConfig
    { chainSyncMessageColor
    , chainSyncMessageText
    , blockFetchMessageColor
    , blockFetchMessageText
    }
  now
  ( SimVizModel
      _events
      PraosSimVizState
        { vizWorldShape = WorldShape{worldDimensions}
        , vizNodePos
        , vizNodeLinks
        , vizMsgsInTransit
        }
    )
  screenSize = do
    renderLinks
    renderNodes
   where
    renderNodes = do
      Cairo.save
      Cairo.setLineWidth 3
      sequence_
        [ do
          Cairo.arc x y 25 0 (pi * 2)
          Cairo.setSourceRGB 0.7 0.7 0.7
          Cairo.fillPreserve
          Cairo.setSourceRGB 0 0 0
          Cairo.stroke
        | (_node, pos) <- Map.toList vizNodePos
        , let (Point x y) = simPointToPixel worldDimensions screenSize pos
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
            (TcpSimVizConfig $ either chainSyncMessageColor blockFetchMessageColor . coerce)
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
        , Just msgLabel <- [either chainSyncMessageText blockFetchMessageText $ coerce msg]
        ]
