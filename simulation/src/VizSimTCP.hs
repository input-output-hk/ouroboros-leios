{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module VizSimTCP where

import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Graphics.Rendering.Cairo as Cairo
import ModelTCP
import P2P
import SimTCPLinks
import SimTypes (LabelLink (..), LabelNode (..), NodeId, Point (..))
import TimeCompat
import Viz
import VizSim
import VizUtils

------------------------------------------------------------------------------
-- The vizualisation model
--

-- | The vizualisation data model for the tcp simulation
type TcpSimVizModel =
  SimVizModel
    TcpSimEvent
    TcpSimVizState

-- | The vizualisation state within the data model for the tcp simulation
data TcpSimVizState = TcpSimVizState
  { vizNodePos :: Map NodeId Point
  , vizNodeLinks :: Set Link
  , vizMsgsInTransit ::
      Map
        (NodeId, NodeId)
        [(TestMessage, TcpMsgForecast, [TcpMsgForecast])]
  , vizMsgsAtNode :: Map NodeId [TestMessage]
  , vizTcpEvents :: [TcpEvent TestMessage] -- for plotting charts
  }

-- | Make the vizualisation model for the tcp simulation from a simulation
-- trace.
tcpSimVizModel ::
  TcpSimTrace ->
  VizModel TcpSimVizModel
tcpSimVizModel =
  simVizModel
    (const accumEventVizState)
    pruneVisState
    initVizState
 where
  initVizState =
    TcpSimVizState
      { vizNodePos = Map.empty
      , vizNodeLinks = Set.empty
      , vizMsgsInTransit = Map.empty
      , vizMsgsAtNode = Map.empty
      , vizTcpEvents = []
      }

  accumEventVizState ::
    TcpSimEvent ->
    TcpSimVizState ->
    TcpSimVizState
  accumEventVizState (TcpSimEventSetup nodes links) vs =
    vs
      { vizNodePos = Map.fromList (map (fmap toPoint) nodes)
      , vizNodeLinks = Set.fromList links
      }
   where
    toPoint :: (Int, Int) -> Point
    toPoint (x, y) = Point (fromIntegral x) (fromIntegral y)
  accumEventVizState
    ( TcpSimEventTcp
        ( LabelLink
            nfrom
            nto
            event@(TcpSendMsg msg msgforecast msgforecasts)
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
        , vizTcpEvents = event : vizTcpEvents vs
        }
  accumEventVizState (TcpSimEventNode (LabelNode nid (MsgArrive msg))) vs =
    vs
      { vizMsgsAtNode =
          Map.insertWith (flip (++)) nid [msg] (vizMsgsAtNode vs)
      }
  accumEventVizState (TcpSimEventNode (LabelNode nid (MsgDepart msg))) vs =
    vs
      { vizMsgsAtNode =
          Map.adjust (filter (/= msg)) nid (vizMsgsAtNode vs)
      }

  pruneVisState ::
    Time ->
    TcpSimVizState ->
    TcpSimVizState
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
      }

------------------------------------------------------------------------------
-- The vizualisation rendering
--

newtype TcpSimVizConfig msg = TcpSimVizConfig
  { messageColor :: msg -> (Double, Double, Double)
  }

tcpSimVizRender ::
  TcpSimVizConfig TestMessage ->
  VizRender TcpSimVizModel
tcpSimVizRender vizConfig =
  VizRender
    { renderReqSize = (500, 500)
    , renderChanged = \_t _fn _m -> True
    , renderModel = \t _fn m _ -> tcpSimVizRenderModel vizConfig t m
    }

tcpSimVizRenderModel ::
  TcpSimVizConfig TestMessage ->
  Time ->
  SimVizModel event TcpSimVizState ->
  Cairo.Render ()
tcpSimVizRenderModel
  config@TcpSimVizConfig
    { messageColor
    }
  now
  ( SimVizModel
      _events
      TcpSimVizState
        { vizNodePos
        , vizNodeLinks
        , vizMsgsInTransit
        , vizMsgsAtNode
        }
    ) = do
    renderLinks
    renderMessagesAtNodes
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
        | (_node, Point x y) <- Map.toList vizNodePos
        ]
      Cairo.restore

    renderMessagesAtNodes = do
      Cairo.save
      sequence_
        [ do
          Cairo.setSourceRGB r g b
          Cairo.arc x y' 10 0 (2 * pi)
          Cairo.fillPreserve
          Cairo.setSourceRGB 0 0 0
          Cairo.setLineWidth 1
          Cairo.stroke
        | (node, msgs) <- Map.toList vizMsgsAtNode
        , (n, msg) <- zip [1 ..] msgs
        , let Point x y = vizNodePos Map.! node
              y' = y + 16 + 20 * n
              (r, g, b) = messageColor msg
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
          renderMessagesInFlight config now fromPos toPos msgs
          Cairo.restore
          -- the draw the link border on top (without clipping)
          renderPathRoundedRect fromPos toPos 20
          Cairo.setSourceRGB 0 0 0
          Cairo.stroke
        | (fromPos, toPos, msgs) <- linksAndMsgs
        ]
      Cairo.restore
     where
      linksAndMsgs =
        [ (fromPos, toPos, msgs)
        | (fromNode :<- toNode) <- Set.toList vizNodeLinks
        , let (fromPos, toPos) =
                translateLineNormal
                  displace
                  ( vizNodePos Map.! fromNode
                  , vizNodePos Map.! toNode
                  )
              -- For links in both directions, we need to displace them
              -- so they don't overlap each other, but for unidirectional
              -- links we can draw it centrally.
              displace
                | Set.notMember (toNode :<- fromNode) vizNodeLinks = 0
                | otherwise = -10

              msgs =
                Map.findWithDefault
                  []
                  (fromNode, toNode)
                  vizMsgsInTransit
        ]

renderMessagesInFlight ::
  TcpSimVizConfig msg ->
  Time ->
  Point ->
  Point ->
  [(msg, TcpMsgForecast, [TcpMsgForecast])] ->
  Cairo.Render ()
renderMessagesInFlight TcpSimVizConfig{messageColor} now fromPos toPos msgs = do
  sequence_
    [ do
      -- The overall message
      withPoint Cairo.moveTo msgTrailingEdge
      withPoint Cairo.lineTo msgLeadingEdge
      Cairo.setSourceRGBA r g b 0.4
      Cairo.setLineWidth 10
      Cairo.stroke
      -- The TCP message fragments
      sequence_
        [ do
          withPoint Cairo.moveTo (msgfragTrailingEdge `addP` offset)
          withPoint Cairo.lineTo (msgfragLeadingEdge `addP` offset)
          withPoint Cairo.lineTo (msgfragLeadingEdge `addP` negateV offset)
          withPoint Cairo.lineTo (msgfragTrailingEdge `addP` negateV offset)
          Cairo.closePath
        | msgfragforecast <- msgforecasts
        , now >= msgSendLeadingEdge msgfragforecast
        , now <= msgRecvTrailingEdge msgfragforecast
        , let (msgfragTrailingEdge, msgfragLeadingEdge) =
                lineMessageInFlight now fromPos toPos msgfragforecast
              offset =
                scaleV (18 / 2) $
                  unitV $
                    normalV $
                      vector
                        msgfragTrailingEdge
                        msgfragLeadingEdge
        ]
      Cairo.setSourceRGB r g b
      Cairo.fillPreserve
      Cairo.setLineWidth 2
      Cairo.stroke
    | (msg, msgforecast, msgforecasts) <- msgs
    , now <= msgRecvTrailingEdge msgforecast
    , let (r, g, b) = messageColor msg
          (msgTrailingEdge, msgLeadingEdge) =
            lineMessageInFlight now fromPos toPos msgforecast
    ]
  -- The TCP acknowledgements (drawn on top of other messages)
  Cairo.save
  Cairo.setLineWidth 2
  Cairo.setSourceRGB 0 0 0
  sequence_
    [ renderAckInFlight fromPos toPos 18 msgfragforecast
    | (_, msgforecast, msgforecasts) <- msgs
    , now >= msgRecvLeadingEdge msgforecast
    , now <= msgAcknowledgement msgforecast
    , msgfragforecast <- msgforecasts
    , now >= msgRecvLeadingEdge msgfragforecast
    , now <= msgAcknowledgement msgfragforecast
    ]
  Cairo.stroke
  Cairo.restore
 where
  renderAckInFlight ::
    Point ->
    Point ->
    Double ->
    TcpMsgForecast ->
    Cairo.Render ()
  renderAckInFlight
    from
    to
    len
    TcpMsgForecast
      { msgRecvLeadingEdge
      , msgAcknowledgement
      } = do
      withPoint Cairo.moveTo (ackPoint `addP` offset)
      withPoint Cairo.lineTo (ackPoint `addP` negateV offset)
     where
      ackPoint = addP to ackVector
      ackVector = scaleV (-ackFraction) toFromVector
      toFromVector = vector from to
      offset = scaleV (len / 2) (unitV (normalV toFromVector))

      ackFraction =
        realToFrac (now `diffTime` msgRecvLeadingEdge)
          / realToFrac (msgAcknowledgement `diffTime` msgRecvLeadingEdge)

lineMessageInFlight ::
  Time ->
  Point ->
  Point ->
  TcpMsgForecast ->
  (Point, Point)
lineMessageInFlight
  now
  from
  to
  TcpMsgForecast
    { msgSendLeadingEdge
    , msgSendTrailingEdge
    , msgRecvLeadingEdge
    , msgRecvTrailingEdge
    } =
    (trailingEdgePoint, leadingEdgePoint)
   where
    leadingEdgePoint = addP from leadingEdgeVector
    trailingEdgePoint = addP from trailingEdgeVector

    leadingEdgeVector = scaleV leadingEdgeFraction fromToVector
    trailingEdgeVector = scaleV trailingEdgeFraction fromToVector

    fromToVector = vector from to

    leadingEdgeFraction, trailingEdgeFraction :: Double
    leadingEdgeFraction
      | now < msgRecvLeadingEdge =
          realToFrac (now `diffTime` msgSendLeadingEdge)
            / realToFrac (msgRecvLeadingEdge `diffTime` msgSendLeadingEdge)
      | otherwise = 1.0

    trailingEdgeFraction
      | now > msgSendTrailingEdge =
          realToFrac (now `diffTime` msgSendTrailingEdge)
            / realToFrac (msgRecvTrailingEdge `diffTime` msgSendTrailingEdge)
      | otherwise = 0.0
