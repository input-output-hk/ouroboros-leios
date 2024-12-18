{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module LeiosProtocol.Short.VizSimP2P where

import ChanDriver
import Control.Arrow ((&&&))
import Data.Array.Unboxed (Ix, UArray, accumArray, (!))
import Data.Bifunctor (second)
import qualified Data.Colour.SRGB as Colour
import Data.Hashable (hash)
import Data.List (foldl', intercalate, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, maybeToList)
import Data.Monoid (Any)
import Diagrams ((#))
import qualified Diagrams.Backend.Cairo as Dia
import qualified Diagrams.Backend.Cairo.Internal as Dia
import qualified Diagrams.Core as Dia
import qualified Diagrams.Prelude as Dia
import qualified Diagrams.TwoD.Adjust as Dia
import qualified Graphics.Rendering.Cairo as Cairo
import qualified Graphics.Rendering.Chart.Easy as Chart
import LeiosProtocol.Common hiding (Point)
import LeiosProtocol.Relay
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import LeiosProtocol.Short.SimP2P (exampleTrace2)
import LeiosProtocol.Short.VizSim (
  IBsInRBsReport (..),
  LeiosSimVizModel,
  LeiosSimVizMsgsState (..),
  LeiosSimVizState (..),
  LeiosVizConfig (praosMessageColor),
  LinkPoints (..),
  examplesLeiosSimVizConfig,
  leiosSimVizModel,
  recentRate,
  totalIBsInRBs,
 )
import Linear.V2
import ModelTCP (TcpMsgForecast (..))
import Network.TypedProtocol
import P2P
import PraosProtocol.BlockFetch (Message (..))
import PraosProtocol.PraosNode (PraosMessage (..))
import SimTypes (Point (..), WorldShape (..))
import System.Random (uniformR)
import qualified System.Random as Random
import System.Random.Stateful (mkStdGen)
import Text.Printf (printf)
import Viz
import VizChart
import VizSim
import VizSimTCP (lineMessageInFlight)
import VizUtils

type CairoDiagram = Dia.QDiagram Dia.Cairo V2 Double Any
renderDiagramAt :: (Double, Double) -> (Double, Double) -> CairoDiagram -> Cairo.Render ()
-- the reflection here is fishy, but otherwise text and shapes are upside down.
renderDiagramAt (w, h) pos (Dia.reflectY -> d0) = do
  Cairo.save
  let sizesp = Dia.mkSizeSpec2D (Just w) (Just h)
  let opts = Dia.CairoOptions "" sizesp Dia.RenderOnly True
  let space = Dia.lc Dia.blue $ Dia.rect w h :: CairoDiagram
  let (opts', t, _) = Dia.adjustDia2D Dia.cairoSizeSpec Dia.Cairo opts space
  let pos' = Dia.inv t `Dia.papply` Dia.p2 pos
  let d = Dia.position [(pos', d0)]
  snd (Dia.renderDia Dia.Cairo opts' $ d # Dia.transform t)
  Cairo.restore

messageDiagram :: (MsgTag, Dia.Colour Double) -> CairoDiagram
messageDiagram (tag, c) = Dia.fc c $
  Dia.lc c $
    case tag of
      RB -> Dia.square 16
      IB -> sizedAs $ Dia.triangle 16
      EB -> sizedAs $ Dia.hexagon 16
      VT -> sizedAs $ Dia.strokePath $ Dia.star (Dia.StarSkip 2) (Dia.regPoly 5 16)
 where
  sizedAs = Dia.sizedAs (Dia.square 18 :: CairoDiagram)

messageLegend :: CairoDiagram
messageLegend =
  Dia.fontSizeO 20 $
    Dia.lc Dia.black $
      Dia.hcat
        [Dia.hcat [messageDiagram (tag, Dia.black), textBox s] | (s, tag) <- [("RB", RB), ("IB", IB), ("EB", EB), ("Vote", VT)]]
 where
  textBox s = Dia.alignedText 0.7 0.5 s `Dia.atop` Dia.phantom (Dia.rect (fromIntegral $ length s * 20 + 10) 20 :: CairoDiagram)

------------------------------------------------------------------------------
-- The vizualisation rendering
--
data MsgTag = RB | IB | EB | VT
  deriving (Show, Enum, Bounded)

data LeiosP2PSimVizConfig
  = LeiosP2PSimVizConfig
  { nodeMessageColor :: RankingBlockHeader -> (Double, Double, Double)
  , ibColor :: InputBlockHeader -> (Double, Double, Double)
  , ebColor :: EndorseBlock -> (Double, Double, Double)
  , voteColor :: VoteMsg -> (Double, Double, Double)
  , ptclMessageColor :: LeiosMessage -> Maybe (MsgTag, Dia.Colour Double)
  }

leiosP2PSimVizRender ::
  LeiosP2PSimVizConfig ->
  VizRender LeiosSimVizModel
leiosP2PSimVizRender vizConfig =
  VizRender
    { renderReqSize = (500, 500) -- nominal, should be overridden
    , renderChanged = \_t _fn _m -> True
    , renderModel = \t _fn m sz ->
        leiosP2PSimVizRenderModel vizConfig t m sz
    }

-- TODO: should be a table?
leiosGenCountRender :: VizRender LeiosSimVizModel
leiosGenCountRender =
  VizRender
    { renderReqSize = (400, 24) -- A little taller than font to avoid clipping
    , renderChanged = \_t _fn _m -> True
    , renderModel = \t _fn m sz ->
        leiosP2PSimVizRenderGenCount t m sz
    }
 where
  leiosP2PSimVizRenderGenCount ::
    Time ->
    SimVizModel event LeiosSimVizState ->
    (Double, Double) ->
    Cairo.Render ()
  leiosP2PSimVizRenderGenCount (Time t) (SimVizModel _events st) _screenSize = do
    Cairo.moveTo 5 20
    Cairo.setFontSize 20
    Cairo.setSourceRGB 0 0 0
    let perSec n = fromIntegral (n :: Int) / realToFrac t :: Double
    let rbs = st.vizNumMsgsGenerated
    let ibs = st.ibMsgs.numMsgsGenerated
    let ebs = st.ebMsgs.numMsgsGenerated
    let votes = st.voteMsgs.numMsgsGenerated
    let IBsInRBsReport{..} = totalIBsInRBs st.ibsInRBs
    Cairo.showText $
      intercalate
        ";  "
        [ "Blocks generated: "
            ++ intercalate
              ",  "
              [ printf "%s: %i (%.2f %s/s)" lbl n (perSec n) lbl
              | (n, lbl) <- [(rbs, "RB"), (ibs, "IB"), (ebs, "EB"), (votes, "Vote")]
              ]
        , printf "IBs in RBs: %i (%i%%)" ibsInRBsNum ((ibsInRBsNum * 100) `div` ibs)
        , printf "IBs in EBs: %i (%i%%)" ibsInEBsNum ((ibsInEBsNum * 100) `div` ibs)
        , printf "EBs in RBs: %i (%i%%)" ebsInRBsNum ((ebsInRBsNum * 100) `div` ibs)
        ]

leiosP2PSimVizRenderModel ::
  LeiosP2PSimVizConfig ->
  Time ->
  SimVizModel event LeiosSimVizState ->
  (Double, Double) ->
  Cairo.Render ()
leiosP2PSimVizRenderModel
  LeiosP2PSimVizConfig
    { nodeMessageColor
    , ptclMessageColor
    }
  now
  ( SimVizModel
      _events
      LeiosSimVizState
        { vizWorldShape = WorldShape{worldDimensions}
        , vizNodePos
        , vizNodeLinks
        , vizNodeTip
        , vizMsgsInTransit
        }
    )
  screenSize = do
    renderDiagramAt screenSize (20, 22) messageLegend
    renderLinks
    renderNodes
   where
    renderNodes = do
      Cairo.save
      Cairo.setFontSize 10
      sequence_
        [ do
          Cairo.arc x y 10 0 (pi * 2)
          Cairo.setSourceRGB r g b
          Cairo.fillPreserve
          Cairo.setSourceRGB 0 0 0
          Cairo.stroke
          {-
                       -- Label with message counts, processing and buffer
                       let qlabel = show nqmsgs ++ "," ++ show rqmsgs ++ "," ++ show tqmsgs
                       Cairo.moveTo (x-6) (y-5)
                       Cairo.setSourceRGB 1 1 1  -- white backdrop text for readabilty
                       Cairo.showText qlabel     -- on dark backgrounds
                       Cairo.moveTo (x-7) (y-4)
                       Cairo.setSourceRGB 0 0 0
                       Cairo.showText qlabel

                       let blabel = show nbmsgs ++ "," ++ show rbmsgs ++ "," ++ show tbmsgs
                       Cairo.moveTo (x-6) (y+10)
                       Cairo.setSourceRGB 1 1 1  -- white backdrop text for readabilty
                       Cairo.showText blabel     -- on dark backgrounds
                       Cairo.moveTo (x-7) (y+9)
                       Cairo.setSourceRGB 0 0 0
                       Cairo.showText blabel
          -}
          Cairo.newPath
        | (node, pos) <- Map.toList vizNodePos
        , let Point x y = toScreenPoint pos
              -- qmsgs = fromMaybe [] (Map.lookup node vizMsgsAtNodeQueue)
              -- bmsgs = fromMaybe [] (Map.lookup node vizMsgsAtNodeBuffer)
              --              nqmsgs  = length qmsgs
              --              nbmsgs  = length bmsgs
              (r, g, b) = case Map.lookup node vizNodeTip of
                Just (FullTip hdr) -> nodeMessageColor hdr
                _ -> (0.7, 0.7, 0.7)
                --              rqmsgs  = maybe 0 recentRate (Map.lookup node vizMsgsAtNodeRecentQueue)
                --              rbmsgs  = maybe 0 recentRate (Map.lookup node vizMsgsAtNodeRecentBuffer)
                --              tqmsgs  = fromMaybe 0 (Map.lookup node vizMsgsAtNodeTotalQueue)
                --              tbmsgs  = fromMaybe 0 (Map.lookup node vizMsgsAtNodeTotalBuffer)
        ]
      Cairo.restore

    renderLinks = do
      Cairo.save
      Cairo.setLineCap Cairo.LineCapButt
      Cairo.setLineWidth 1
      Cairo.setSourceRGB 0.4 0.4 0.4
      -- draw all the lines
      Cairo.save
      sequence_
        [ case classifyInFlightMsgs msgs of
          -- We don't even draw links that are inactive
          MsgsInFlightNone -> return ()
          -- Similarly, all links will have boring control messages
          -- it'd be too much details
          MsgsInFlightControl -> return ()
          -- We draw with a dotted line
          MsgsInFlightNonBallistic ->
            case catMaybes [snd <$> ptclMessageColor msg | (msg, _, _) <- msgs] of
              [] -> return ()
              ((toSRGB -> (r, g, b)) : _) -> do
                Cairo.setSourceRGB r g b
                Cairo.setLineWidth 1
                Cairo.setDash [10, 5] 0
                case vizNodeLinks Map.! (fromNode, toNode) of
                  LinkPointsNoWrap fromPos toPos -> do
                    withPoint Cairo.moveTo (toScreenPoint fromPos)
                    withPoint Cairo.lineTo (toScreenPoint toPos)
                    Cairo.stroke
                  LinkPointsWrap fromPos toPos fromPos' toPos' -> do
                    withPoint Cairo.moveTo (toScreenPoint fromPos)
                    withPoint Cairo.lineTo (toScreenPoint toPos)
                    Cairo.stroke
                    withPoint Cairo.moveTo (toScreenPoint fromPos')
                    withPoint Cairo.lineTo (toScreenPoint toPos')
                    Cairo.stroke

          -- We draw with a full line
          MsgsInFlightBallistic ->
            case catMaybes [snd <$> ptclMessageColor msg | (msg, _, _) <- msgs] of
              [] -> return ()
              ((toSRGB -> (r, g, b)) : _) -> do
                Cairo.setSourceRGB r g b
                Cairo.setDash [] 0
                Cairo.setLineWidth 2
                case vizNodeLinks Map.! (fromNode, toNode) of
                  LinkPointsNoWrap fromPos toPos -> do
                    withPoint Cairo.moveTo (toScreenPoint fromPos)
                    withPoint Cairo.lineTo (toScreenPoint toPos)
                    Cairo.stroke
                  LinkPointsWrap fromPos toPos fromPos' toPos' -> do
                    withPoint Cairo.moveTo (toScreenPoint fromPos)
                    withPoint Cairo.lineTo (toScreenPoint toPos)
                    Cairo.stroke
                    withPoint Cairo.moveTo (toScreenPoint fromPos')
                    withPoint Cairo.lineTo (toScreenPoint toPos')
                    Cairo.stroke
        | ((fromNode, toNode), msgs) <- Map.toList vizMsgsInTransit
        ]
      Cairo.restore
      -- draw the messages in flight on top
      sequence_
        [ case vizNodeLinks Map.! (fromNode, toNode) of
          LinkPointsNoWrap fromPos toPos -> do
            let (msgTrailingEdge, _msgLeadingEdge) =
                  lineMessageInFlight now fromPos toPos msgforecast
                Point x y = toScreenPoint msgTrailingEdge
            renderDiagramAt screenSize (x, y) $ messageDiagram msgViz
          LinkPointsWrap fromPos toPos fromPos' toPos' -> do
            let (msgTrailingEdge, _msgLeadingEdge) =
                  lineMessageInFlight now fromPos toPos msgforecast
                Point x y = toScreenPoint msgTrailingEdge
            renderDiagramAt screenSize (x, y) $ messageDiagram msgViz
            let (msgTrailingEdge', _msgLeadingEdge) =
                  lineMessageInFlight now fromPos' toPos' msgforecast
                Point x' y' = toScreenPoint msgTrailingEdge'
            renderDiagramAt screenSize (x', y') $ messageDiagram msgViz
        | ((fromNode, toNode), msgs) <- Map.toList vizMsgsInTransit
        , (msg, msgforecast, _msgforecasts) <- msgs
        , now >= msgSendTrailingEdge msgforecast
        , now <= msgRecvTrailingEdge msgforecast
        , msgViz <- maybeToList (ptclMessageColor msg)
        ]
      Cairo.restore

    toScreenPoint = simPointToPixel worldDimensions screenSize

data MsgsInFlightClassification
  = MsgsInFlightNone
  | MsgsInFlightControl
  | MsgsInFlightNonBallistic
  | MsgsInFlightBallistic
  deriving (Eq, Ord, Enum, Bounded, Ix)

classifyInFlightMsgs ::
  [(LeiosMessage, TcpMsgForecast, [TcpMsgForecast])] ->
  MsgsInFlightClassification
classifyInFlightMsgs = classifyInFlightMsgs' isLeiosMessageControl
classifyInFlightMsgs' ::
  (msg -> Bool) ->
  [(msg, TcpMsgForecast, [TcpMsgForecast])] ->
  MsgsInFlightClassification
classifyInFlightMsgs' _isControl [] = MsgsInFlightNone
classifyInFlightMsgs' isControl msgs
  | all control msgs = MsgsInFlightControl
  | all ballistic msgs = MsgsInFlightBallistic
  | otherwise = MsgsInFlightNonBallistic
 where
  -- We rely on contiguous forecast fragments having been merged,
  -- see mergeAdjacentForecasts
  ballistic (_msg, _msgforecast, _msgforecasts@[_]) = True
  ballistic _ = False

  -- In leios some msgs (empty rbs (before first pipeline ends), ebs,
  -- and votes) might be small, but shouldn't be considered control.
  -- We take an extra predicate.
  control (msg, _msgforecast, _msgforecasts) = isControl msg

------------------------------------------------------------------------------
-- The charts
--

diffusionLatencyPerStakeFraction :: Int -> Time -> [Time] -> [(DiffTime, Double)]
diffusionLatencyPerStakeFraction nnodes created arrivals =
  [ (latency, percent)
  | (arrival, n) <- zip (reverse arrivals) [1 :: Int ..]
  , let !latency = arrival `diffTime` created
        !percent = fromIntegral n / fromIntegral nnodes
  ]

chartDiffusionLatency ::
  LeiosP2PSimVizConfig ->
  MsgTag ->
  VizRender LeiosSimVizModel
chartDiffusionLatency cfg@LeiosP2PSimVizConfig{nodeMessageColor} tag =
  chartVizRender 25 $
    \_
     _
     ( SimVizModel
        _
        st@LeiosSimVizState
          { vizNodePos
          }
      ) -> case tag of
        RB -> theChart (show tag) vizNodePos nodeMessageColor st.vizMsgsDiffusionLatency
        IB -> theChart (show tag) vizNodePos cfg.ibColor st.ibDiffusionLatency
        EB -> theChart (show tag) vizNodePos cfg.ebColor st.ebDiffusionLatency
        VT -> theChart (show tag) vizNodePos cfg.voteColor st.voteDiffusionLatency
 where
  theChart lbl nodePos nodeMsgColor msgsDiffusionLatency =
    (Chart.def :: Chart.Layout DiffTime Chart.Percent)
      { Chart._layout_title = "Diffusion latency" ++ " (" ++ lbl ++ ")"
      , Chart._layout_title_style = Chart.def{Chart._font_size = 15}
      , Chart._layout_y_axis =
          (Chart.def :: Chart.LayoutAxis Chart.Percent)
            { Chart._laxis_generate =
                Chart.scaledAxis Chart.def{Chart._la_nLabels = 10} (0, 1)
            , Chart._laxis_title = "Stake fraction reached"
            }
      , Chart._layout_x_axis =
          Chart.def
            { Chart._laxis_title = "Time (seconds)"
            }
      , Chart._layout_plots =
          [ Chart.toPlot $
            Chart.def
              { Chart._plot_lines_values = [timeseries]
              , Chart._plot_lines_style =
                  let (r, g, b) = nodeMsgColor blk
                   in Chart.def
                        { Chart._line_color = Chart.opaque (Colour.sRGB r g b)
                        }
              }
          | let nnodes = Map.size nodePos
          , (blk, _nid, created, arrivals) <- Map.elems msgsDiffusionLatency
          , let timeseries =
                  map (second Chart.Percent) $
                    diffusionLatencyPerStakeFraction nnodes created arrivals
          ]
      }

chartDiffusionImperfection ::
  P2PTopography ->
  DiffTime ->
  DiffTime ->
  LeiosP2PSimVizConfig ->
  VizRender LeiosSimVizModel
chartDiffusionImperfection
  p2ptopography
  processingDelay
  serialisationDelay
  LeiosP2PSimVizConfig{nodeMessageColor}
    | Map.size (p2pNodes p2ptopography) > 100 =
        nullVizRender
    | otherwise =
        chartVizRender 25 $
          \_
           _
           (SimVizModel _ LeiosSimVizState{vizMsgsDiffusionLatency}) ->
              (Chart.def :: Chart.Layout DiffTime DiffTime)
                { Chart._layout_title = "Diffusion latency imperfection"
                , Chart._layout_title_style = Chart.def{Chart._font_size = 15}
                , Chart._layout_y_axis =
                    Chart.def
                      { Chart._laxis_title = "Time behind perfect (seconds)"
                      }
                , Chart._layout_x_axis =
                    Chart.def
                      { Chart._laxis_title = "Time (seconds)"
                      }
                , Chart._layout_plots =
                    [ Chart.toPlot $
                      Chart.def
                        { Chart._plot_lines_values = [timeseries]
                        , Chart._plot_lines_style =
                            let (r, g, b) = nodeMessageColor blk
                             in Chart.def
                                  { Chart._line_color = Chart.opaque (Colour.sRGB r g b)
                                  }
                        }
                    | (blk, nid, created, arrivals) <- Map.elems vizMsgsDiffusionLatency
                    , let timeseries =
                            [ (latencyActual, imperfection)
                            | (arrivalActual, latencyIdeal) <-
                                zip
                                  (reverse arrivals)
                                  ( p2pGraphIdealDiffusionTimesFromNode
                                      idealDiffusionTimes
                                      nid
                                  )
                            , let !latencyActual = arrivalActual `diffTime` created
                                  !imperfection = latencyActual - latencyIdeal
                            ]
                    ]
                }
   where
    idealDiffusionTimes :: P2PIdealDiffusionTimes
    idealDiffusionTimes =
      p2pGraphIdealDiffusionTimes
        p2ptopography
        (const processingDelay)
        (\_ _ linkLatency -> 3 * linkLatency + serialisationDelay)

chartBandwidth :: VizRender LeiosSimVizModel
chartBandwidth =
  chartVizRender 25 $
    \_
     _
     ( SimVizModel
        _
        LeiosSimVizState
          { vizMsgsAtNodeRecentQueue
          , vizMsgsAtNodeRecentBuffer
          }
      ) ->
        (Chart.def :: Chart.Layout Double Double)
          { Chart._layout_title = "Distribution of block frequency"
          , Chart._layout_title_style = Chart.def{Chart._font_size = 15}
          , Chart._layout_x_axis =
              Chart.def
                { Chart._laxis_generate =
                    Chart.scaledAxis Chart.def{Chart._la_nLabels = maxX} (0, maxX)
                , Chart._laxis_title = "Count of events within last 30 seconds"
                }
          , Chart._layout_y_axis =
              Chart.def
                { Chart._laxis_generate =
                    Chart.scaledAxis Chart.def{Chart._la_nLabels = 4} (0, 0.35)
                , Chart._laxis_title = "Number of nodes in each bin (normalised)"
                }
          , Chart._layout_plots =
              [ bandwidthHistPlot
                "CPU (block validation completion)"
                Chart.red
                ( map
                    ((fromIntegral :: Int -> Double) . recentRate)
                    (Map.elems vizMsgsAtNodeRecentBuffer)
                )
              | not (Map.null vizMsgsAtNodeRecentBuffer)
              ]
                ++ [ bandwidthHistPlot
                    "Network (block arrival)"
                    Chart.blue
                    ( map
                        ((fromIntegral :: Int -> Double) . recentRate)
                        (Map.elems vizMsgsAtNodeRecentQueue)
                    )
                   | not (Map.null vizMsgsAtNodeRecentQueue)
                   ]
          }
 where
  maxX :: Num a => a
  maxX = 15

  bandwidthHistPlot title color values =
    Chart.histToPlot $
      Chart.defaultNormedPlotHist
        { Chart._plot_hist_title = title
        , Chart._plot_hist_values = values
        , Chart._plot_hist_range = Just (0, maxX)
        , Chart._plot_hist_bins = maxX
        , Chart._plot_hist_fill_style =
            Chart.def
              { Chart._fill_color =
                  Chart.withOpacity color 0.4
              }
        , Chart._plot_hist_line_style =
            Chart.def
              { Chart._line_color =
                  Chart.opaque color
              }
        }

chartLinkUtilisation :: VizRender LeiosSimVizModel
chartLinkUtilisation =
  chartVizRender 25 $
    \_
     _
     ( SimVizModel
        _
        LeiosSimVizState
          { vizMsgsInTransit
          }
      ) ->
        let counts :: UArray MsgsInFlightClassification Int
            counts =
              accumArray
                (\i () -> i + 1)
                0
                (minBound, maxBound)
                $ [ (classifyInFlightMsgs msgs, ())
                  | msgs <- Map.elems vizMsgsInTransit
                  ]
         in (Chart.def :: Chart.PieLayout)
              { Chart._pie_title = "TCP link usage"
              , Chart._pie_title_style = Chart.def{Chart._font_size = 15}
              , Chart._pie_plot =
                  Chart.def
                    { Chart._pie_data =
                        [ let v = counts ! MsgsInFlightNone
                           in Chart.def
                                { Chart._pitem_label = "Idle (" ++ show v ++ ")"
                                , Chart._pitem_value = fromIntegral v
                                }
                        , let v = counts ! MsgsInFlightControl
                           in Chart.def
                                { Chart._pitem_label = "Control (" ++ show v ++ ")"
                                , Chart._pitem_value = fromIntegral v
                                }
                        , let v = counts ! MsgsInFlightNonBallistic
                           in Chart.def
                                { Chart._pitem_label = "Non-ballistic (" ++ show v ++ ")"
                                , Chart._pitem_value = fromIntegral v
                                }
                        , let v = counts ! MsgsInFlightBallistic
                           in Chart.def
                                { Chart._pitem_label = "Ballistic (" ++ show v ++ ")"
                                , Chart._pitem_value = fromIntegral v
                                }
                        ]
                    , Chart._pie_colors =
                        [ lightBlueShade 0.9
                        , lightBlueShade 0.7
                        , lightBlueShade 0.3
                        , lightBlueShade 0
                        ]
                    }
              }
 where
  lightBlueShade :: Double -> Chart.AlphaColour Double
  lightBlueShade x =
    Chart.withOpacity Chart.white x
      `Chart.atop` Chart.opaque Chart.blue

isLeiosMessageControl :: LeiosMessage -> Bool
isLeiosMessageControl msg0 =
  case msg0 of
    PraosMsg msg ->
      case msg of
        PraosMessage (Right (ProtocolMessage (SomeMessage MsgBlock{}))) -> False
        _ -> True
    RelayIB msg -> isRelayMessageControl msg
    RelayEB msg -> isRelayMessageControl msg
    RelayVote msg -> isRelayMessageControl msg

isRelayMessageControl :: RelayMessage id header body -> Bool
isRelayMessageControl (ProtocolMessage (SomeMessage msg)) = case msg of
  MsgRespondBodies _bodies -> False
  _otherwise -> True

-- | takes stage length, assumes pipelines start at Slot 0.
defaultVizConfig :: Int -> LeiosP2PSimVizConfig
defaultVizConfig stageLength =
  LeiosP2PSimVizConfig
    { nodeMessageColor = testNodeMessageColor
    , ptclMessageColor = testPtclMessageColor
    , voteColor = toSRGB . voteColor
    , ebColor = toSRGB . ebColor
    , ibColor = toSRGB . pipelineColor Propose . (hash . (.id) &&& (.slot))
    }
 where
  testPtclMessageColor ::
    LeiosMessage ->
    Maybe (MsgTag, Dia.Colour Double)
  testPtclMessageColor msg0 =
    case msg0 of
      PraosMsg msg ->
        (RB,) <$> case msg of
          PraosMessage (Right (ProtocolMessage (SomeMessage MsgBlock{}))) -> do
            let (r, g, b) = praosMessageColor examplesLeiosSimVizConfig msg
            Just $ Dia.sRGB r g b
          _ -> Nothing
      RelayIB msg -> (IB,) <$> relayMessageColor ibColor msg
      RelayEB msg -> (EB,) <$> relayMessageColor ebColor msg
      RelayVote msg -> (VT,) <$> relayMessageColor voteColor msg
  ibColor = pipelineColor Propose . (hash . (.id) &&& (.slot))
  ebColor = pipelineColor Endorse . (hash . (.id) &&& (.slot))
  voteColor = pipelineColor Vote . (hash . (.id) &&& (.slot))
  relayMessageColor :: (body -> Dia.Colour Double) -> RelayMessage id header body -> Maybe (Dia.Colour Double)
  relayMessageColor f (ProtocolMessage (SomeMessage msg)) = case msg of
    MsgRespondBodies bodies -> Just $ blendColors $ map (f . snd) bodies
    _otherwise -> Nothing
  testNodeMessageColor :: RankingBlockHeader -> (Double, Double, Double)
  testNodeMessageColor = blockHeaderColorAsBody
  -- alternating cold and warm colours for visual contrast.
  palettes =
    map snd $
      sortOn fst $
        zip [0 :: Int, 2 ..] [Dia.orangered, Dia.red, Dia.magenta, Dia.plum]
          ++ zip [1, 3 ..] [Dia.blue, Dia.cyan, Dia.lime, Dia.yellow]
  palettes_num = length palettes
  paletteColor p seed = Dia.blend f Dia.white c
   where
    -- TODO?: better palettes than gradients on a color
    c = palettes !! p
    f = fst $ uniformR (0, 0.5) seed
  pipelineColor :: Stage -> (Int, SlotNo) -> Dia.Colour Double
  pipelineColor slotStage (i, slot) = case stageRange' stageLength slotStage slot Propose of
    Just (fromEnum -> startOfPipeline, _) ->
      let
        -- every `stageLength` a new pipeline begins
        pipeline_idx = startOfPipeline `div` stageLength
        -- There are at most |stages| active pipelines at once,
        -- however we use a few more palettes to avoid reusing the
        -- same color too soon in time.
        palette_idx = pipeline_idx `mod` palettes_num
       in
        paletteColor palette_idx (mkStdGen i)
    Nothing -> Dia.black

-- might be ugly blending, but in practice it's going to be singleton lists?
blendColors :: [Dia.Colour Double] -> Dia.Colour Double
blendColors [x] = x
blendColors [] = Dia.black
blendColors (x : xs) = foldl' (Dia.blend 0.5) x xs

toSRGB :: Dia.Colour Double -> (Double, Double, Double)
toSRGB (Dia.toSRGB -> Dia.RGB r g b) = (r, g, b)

example2 :: Int -> Int -> Maybe P2PTopography -> Visualization
example2 seed sliceLength maybeP2PTopography =
  slowmoVisualization 0.5 $
    Viz model $
      LayoutAbove
        [ LayoutBeside [layoutLabelTime, Layout leiosGenCountRender]
        , LayoutBeside
            [ LayoutReqSize 1200 1000 $
                Layout $
                  leiosP2PSimVizRender config
            , LayoutBeside
                [ LayoutAbove
                    [ LayoutReqSize 350 250 $
                      Layout $
                        chartDiffusionLatency config tag
                    | -- , LayoutReqSize 350 300 $
                    --     Layout $
                    --       chartDiffusionImperfection
                    --         p2pTopography
                    --         0.1
                    --         (96 / 1000)
                    --         config
                    tag <- [IB, EB, VT, RB]
                    ]
                , LayoutAbove
                    [ LayoutReqSize 350 300 $
                        Layout chartBandwidth
                    , LayoutReqSize 350 300 $
                        Layout chartLinkUtilisation
                    ]
                ]
            ]
        ]
 where
  config = defaultVizConfig 5
  rng0 = mkStdGen seed
  (rng1, rng2) = Random.split rng0
  p2pTopography =
    flip fromMaybe maybeP2PTopography $
      flip genArbitraryP2PTopography rng1 $
        P2PTopographyCharacteristics
          { p2pWorldShape =
              WorldShape
                { worldDimensions = (0.600, 0.300)
                , worldIsCylinder = True
                }
          , p2pNumNodes = 100
          , p2pNodeLinksClose = 5
          , p2pNodeLinksRandom = 5
          }
  model = leiosSimVizModel (exampleTrace2 rng2 sliceLength p2pTopography)
