{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module VizSimRelay where

import           Data.Maybe
import qualified Data.Map.Strict as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.PQueue.Min as PQ
import           Data.PQueue.Min (MinQueue)

import           Control.Monad.Class.MonadTime.SI (Time, addTime)
import           Control.Exception (assert)

import qualified Graphics.Rendering.Cairo as Cairo

import ModelTCP
import SimTCPLinks (NodeId(..), LabelNode(..), LabelLink(..))
import SimRelay
import Viz
import VizSim
import VizSimTCP (TcpSimVizConfig(..), renderMessagesInFlight,
                  lineMessageInFlight)
import VizUtils


------------------------------------------------------------------------------
-- The vizualisation model
--

-- | The vizualisation data model for the tcp simulation
type RelaySimVizModel =
       SimVizModel
         RelaySimEvent
         RelaySimVizState

-- | The vizualisation state within the data model for the tcp simulation
data RelaySimVizState =
     RelaySimVizState {
       vizWorldSize     :: !(Double, Double),
       vizNodePos       :: !(Map NodeId (Double, Double)),
       vizNodeLinks     :: !(Set (NodeId, NodeId)),
       vizMsgsInTransit :: !(Map (NodeId, NodeId)
                               [(TestBlockRelayMessage,
                                 TcpMsgForecast, [TcpMsgForecast])]),
       vizMsgsAtNodeQueue  :: !(Map NodeId [TestBlock]),
       vizMsgsAtNodeBuffer :: !(Map NodeId [TestBlock]),
       vizMsgsAtNodeRecentQueue  :: !(Map NodeId RecentRate),
       vizMsgsAtNodeRecentBuffer :: !(Map NodeId RecentRate),
       vizMsgsAtNodeTotalQueue   :: !(Map NodeId Int),
       vizMsgsAtNodeTotalBuffer  :: !(Map NodeId Int),
       vizNumMsgsGenerated       :: !Int,
       vizMsgsDiffusionLatency   :: !(Map TestBlockId (TestBlock, NodeId, Time, [Time]))
     }


-- | Make the vizualisation model for the relay simulation from a simulation
-- trace.
relaySimVizModel :: RelaySimTrace
                 -> VizModel RelaySimVizModel
relaySimVizModel =
    simVizModel
      accumEventVizState
      pruneVisState
      initVizState
  where
    initVizState =
      RelaySimVizState {
        vizWorldSize     = (0,0),
        vizNodePos       = Map.empty,
        vizNodeLinks     = Set.empty,
        vizMsgsInTransit = Map.empty,
        vizMsgsAtNodeQueue  = Map.empty,
        vizMsgsAtNodeBuffer = Map.empty,
        vizMsgsAtNodeRecentQueue  = Map.empty,
        vizMsgsAtNodeRecentBuffer = Map.empty,
        vizMsgsAtNodeTotalQueue   = Map.empty,
        vizMsgsAtNodeTotalBuffer  = Map.empty,
        vizNumMsgsGenerated       = 0,
        vizMsgsDiffusionLatency   = Map.empty
      }

    accumEventVizState :: Time
                       -> RelaySimEvent
                       -> RelaySimVizState
                       -> RelaySimVizState
    accumEventVizState _now (RelaySimEventSetup size nodes links) vs =
        vs {
          vizWorldSize = size,
          vizNodePos   = nodes,
          vizNodeLinks = links
        }

    accumEventVizState _now (RelaySimEventTcp
                             (LabelLink nfrom nto
                               (TcpSendMsg msg msgforecast msgforecasts))) vs =
        vs {
          vizMsgsInTransit =
            Map.insertWith (flip (++)) (nfrom, nto)
                           [(msg, msgforecast, msgforecasts)]
                           (vizMsgsInTransit vs)
        }

    accumEventVizState now (RelaySimEventNode (LabelNode nid (RelayNodeEventEnterQueue msg))) vs =
        vs {
          vizMsgsAtNodeQueue =
            Map.insertWith (flip (++)) nid [msg] (vizMsgsAtNodeQueue vs),
          vizMsgsAtNodeRecentQueue =
            Map.alter (Just . recentAdd now . fromMaybe recentEmpty)
                      nid (vizMsgsAtNodeRecentQueue vs),
          vizMsgsAtNodeTotalQueue =
            Map.insertWith (+) nid 1 (vizMsgsAtNodeTotalQueue vs)
        }
    accumEventVizState now (RelaySimEventNode (LabelNode nid (RelayNodeEventEnterBuffer msg))) vs =
        vs {
          vizMsgsAtNodeBuffer =
            Map.insertWith (flip (++)) nid [msg] (vizMsgsAtNodeBuffer vs),
          vizMsgsAtNodeQueue =
            Map.adjust (filter (\msg' -> testBlockId msg' /= testBlockId msg))
                       nid (vizMsgsAtNodeQueue vs),
          vizMsgsAtNodeRecentBuffer =
            Map.alter (Just . recentAdd now . fromMaybe recentEmpty)
                      nid (vizMsgsAtNodeRecentBuffer vs),
          vizMsgsAtNodeTotalBuffer =
            Map.insertWith (+) nid 1 (vizMsgsAtNodeTotalBuffer vs),
          vizMsgsDiffusionLatency =
            Map.adjust (\(blk, nid', created, arrivals) ->
                           (blk, nid', created, (now:arrivals)))
                       (testBlockId msg) (vizMsgsDiffusionLatency vs)
        }
    accumEventVizState _now (RelaySimEventNode (LabelNode nid (RelayNodeEventRemove msg))) vs =
        vs {
          vizMsgsAtNodeBuffer =
            Map.adjust (filter (\msg' -> testBlockId msg' /= testBlockId msg))
                       nid (vizMsgsAtNodeBuffer vs),
          vizMsgsAtNodeQueue =
            Map.adjust (filter (\msg' -> testBlockId msg' /= testBlockId msg))
                       nid (vizMsgsAtNodeQueue vs)
        }
    accumEventVizState now (RelaySimEventNode (LabelNode nid (RelayNodeEventGenerate msg))) vs =
        vs {
          vizMsgsAtNodeBuffer =
            Map.insertWith (flip (++)) nid [msg] (vizMsgsAtNodeBuffer vs),
          vizMsgsAtNodeRecentBuffer =
            Map.alter (Just . recentAdd now . fromMaybe recentEmpty)
                      nid (vizMsgsAtNodeRecentBuffer vs),
          vizMsgsAtNodeTotalBuffer =
            Map.insertWith (+) nid 1 (vizMsgsAtNodeTotalBuffer vs),
          vizNumMsgsGenerated = vizNumMsgsGenerated vs + 1,
          vizMsgsDiffusionLatency =
            assert (not (testBlockId msg `Map.member` vizMsgsDiffusionLatency vs)) $
            Map.insert (testBlockId msg) (msg, nid, now, [now])
                       (vizMsgsDiffusionLatency vs)
        }

    pruneVisState :: Time
                  -> RelaySimVizState
                  -> RelaySimVizState
    pruneVisState now vs =
        vs {
          vizMsgsInTransit =
            Map.map (filter (\(_, msgforecast, _) ->
                       now <= msgAcknowledgement msgforecast))
                    (vizMsgsInTransit vs),
          vizMsgsAtNodeRecentQueue =
            Map.map (recentPrune secondsAgo1) (vizMsgsAtNodeRecentQueue vs),
          vizMsgsAtNodeRecentBuffer =
            Map.map (recentPrune secondsAgo1) (vizMsgsAtNodeRecentBuffer vs),
          vizMsgsDiffusionLatency =
            Map.filter (\(_,_,t,_) -> t >= secondsAgo10) (vizMsgsDiffusionLatency vs)
        }
      where
        secondsAgo1 :: Time
        secondsAgo1 = addTime (-1) now

        secondsAgo10 :: Time
        secondsAgo10 = addTime (-10) now


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
    _           -> RecentRate pq


------------------------------------------------------------------------------
-- The vizualisation rendering
--

data RelaySimVizConfig =
     RelaySimVizConfig {
       nodeMessageColor :: TestBlock             -> (Double, Double, Double),
       ptclMessageColor :: TestBlockRelayMessage -> (Double, Double, Double),
       nodeMessageText  :: TestBlock             -> Maybe String,
       ptclMessageText  :: TestBlockRelayMessage -> Maybe String
     }

relaySimVizRender :: RelaySimVizConfig
                  -> VizRender RelaySimVizModel
relaySimVizRender vizConfig =
    VizRender {
      renderReqSize = (500,500),
      renderChanged = \_t _fn _m -> True,
      renderModel   = \ t _fn  m sz -> relaySimVizRenderModel vizConfig t m sz
    }

relaySimVizRenderModel :: RelaySimVizConfig
                       -> Time
                       -> SimVizModel event RelaySimVizState
                       -> (Double, Double)
                       -> Cairo.Render ()
relaySimVizRenderModel RelaySimVizConfig {
                         nodeMessageColor,
                         ptclMessageColor,
                         nodeMessageText,
                         ptclMessageText
                       }
                       now
                       (SimVizModel _events
                          RelaySimVizState {
                            vizWorldSize,
                            vizNodePos,
                            vizNodeLinks,
                            vizMsgsInTransit,
                            vizMsgsAtNodeQueue,
                            vizMsgsAtNodeBuffer
                          })
                       screenSize = do
      renderLinks
      renderMessagesAtNodes
      renderNodes
  where
    renderNodes = do
      Cairo.save
      Cairo.setLineWidth 3
      sequence_
        [ do Cairo.arc x y 25 0 (pi * 2)
             Cairo.setSourceRGB 0.7 0.7 0.7
             Cairo.fillPreserve
             Cairo.setSourceRGB 0 0 0
             Cairo.stroke
        | (_node, pos) <- Map.toList vizNodePos
        , let (x,y) = simPointToPixel vizWorldSize screenSize pos
        ]
      Cairo.restore

    renderMessagesAtNodes = do
      Cairo.save
      sequence_
        [ do Cairo.setSourceRGB r g b
             Cairo.arc (x-10) y' 10 0 (2 * pi)
             Cairo.fillPreserve
             Cairo.setSourceRGB 0 0 0
             Cairo.setLineWidth 1
             Cairo.stroke
             case nodeMessageText msg of
               Nothing  -> return ()
               Just txt -> do
                 Cairo.moveTo (x-32) (y'+5)
                 Cairo.showText txt
                 Cairo.newPath
        | (node, msgs) <- Map.toList vizMsgsAtNodeQueue
        , (n, msg) <- zip [1..] msgs
        , let (x,y)   = simPointToPixel vizWorldSize screenSize
                                        (vizNodePos Map.! node)
              y'      = y + 16 + 20 * n
              (r,g,b) = nodeMessageColor msg
        ]
      sequence_
        [ do Cairo.setSourceRGB r g b
             Cairo.arc (x+10) y' 10 0 (2 * pi)
             Cairo.fillPreserve
             Cairo.setSourceRGB 0 0 0
             Cairo.setLineWidth 1
             Cairo.stroke
             case nodeMessageText msg of
               Nothing  -> return ()
               Just txt -> do
                 Cairo.moveTo (x+22) (y'+5)
                 Cairo.showText txt
                 Cairo.newPath
        | (node, msgs) <- Map.toList vizMsgsAtNodeBuffer
        , (n, msg) <- zip [1..] msgs
        , let (x,y)   = simPointToPixel vizWorldSize screenSize
                                        (vizNodePos Map.! node)
              y'      = y + 16 + 20 * n
              (r,g,b) = nodeMessageColor msg
        ]
      Cairo.restore

    renderLinks = do
      Cairo.save
      Cairo.setLineCap Cairo.LineCapButt
      Cairo.setLineWidth 3
      sequence_
        [ do Cairo.save
             renderPathRoundedRect fromPos toPos 20
             Cairo.setSourceRGB 0.9 0.9 0.9
             Cairo.fillPreserve
             Cairo.clip
             Cairo.newPath
             -- draw all the messages within the clipping region of the link
             renderMessagesInFlight (TcpSimVizConfig ptclMessageColor)
                                    now fromPos toPos msgs
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
          | (fromNode, toNode) <- Set.toList vizNodeLinks
          , let (fromPos, toPos) =
                  translateLineNormal displace
                    (simPointToPixel vizWorldSize screenSize (vizNodePos Map.! fromNode),
                     simPointToPixel vizWorldSize screenSize (vizNodePos Map.! toNode))
                -- For links in both directions, we need to displace them
                -- so they don't overlap each other, but for unidirectional
                -- links we can draw it centrally.
                displace
                  | Set.notMember (toNode, fromNode) vizNodeLinks =   0
                  | otherwise                                     = -10

                msgs = Map.findWithDefault
                         [] (fromNode, toNode)
                         vizMsgsInTransit
         ]

    renderMessageLabelsInFlight fromPos toPos msgs = do
        Cairo.save
        Cairo.setSourceRGB 0.5 0.5 0.5
        Cairo.setFontSize 10
        Cairo.setLineWidth 0.6
        -- draw lines from labels to messages
        sequence_
          [ do uncurry Cairo.moveTo (labelsOrigin `addV` (0,n*10))
               uncurry Cairo.lineTo msgTrailingEdge
          | ((_msgLabel, msgforecast), n) <- zip msgLabels [0..]
          , let (msgTrailingEdge, _msgLeadingEdge) =
                  lineMessageInFlight now fromPos toPos msgforecast
          ]
        Cairo.stroke
        -- draw the labels themselves
        Cairo.setSourceRGB 0 0 0
        sequence_
          [ do uncurry Cairo.moveTo (labelsOrigin `addV` (0,n*10))
               Cairo.showText msgLabel
               Cairo.newPath
          | ((msgLabel, _), n) <- zip msgLabels [0..] ]
        Cairo.restore
      where
        labelsOrigin = midpointV fromPos toPos `addV` labelsOffset
        labelsOffset = scaleV (-50) $ unitV $ normalV $ vector fromPos toPos
        msgLabels =
          [ (msgLabel, msgforecast)
          | (msg, msgforecast, _) <- msgs
          , now <= msgRecvTrailingEdge msgforecast
          , Just msgLabel <- [ptclMessageText msg]
          ]

