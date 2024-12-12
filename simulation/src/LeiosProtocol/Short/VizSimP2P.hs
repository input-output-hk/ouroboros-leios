{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# HLINT ignore "Use const" #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module LeiosProtocol.Short.VizSimP2P where

import Data.Array.Unboxed (Ix, UArray, accumArray, (!))
import qualified Data.Colour.SRGB as Colour
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, maybeToList)
import qualified Graphics.Rendering.Cairo as Cairo
import qualified Graphics.Rendering.Chart.Easy as Chart

import ChanDriver
import Data.Bifunctor (Bifunctor (bimap), second)
import Data.Coerce
import Data.Hashable (hash)
import Data.List (intercalate)
import Data.Monoid
import LeiosProtocol.Common hiding (Point)
import LeiosProtocol.Relay
import LeiosProtocol.Short
import LeiosProtocol.Short.Node
import LeiosProtocol.Short.SimP2P (exampleTrace2)
import LeiosProtocol.Short.VizSim (
  LeiosSimVizModel,
  LeiosSimVizMsgsState (..),
  LeiosSimVizState (..),
  LeiosVizConfig (praosMessageColor),
  LinkPoints (..),
  examplesLeiosSimVizConfig,
  leiosSimVizModel,
  recentRate,
 )
import ModelTCP (TcpMsgForecast (..), segmentSize)
import Network.TypedProtocol
import P2P
import PraosProtocol.BlockFetch (Message (..))
import PraosProtocol.Common (BlockHeader, FullTip (FullTip), blockHeaderColorAsBody)
import PraosProtocol.PraosNode (PraosMessage (..))
import SimTypes (Point (..), WorldShape (..))
import System.Random (uniformR)
import System.Random.Stateful (mkStdGen)
import Text.Printf (printf)
import Viz
import VizChart
import VizSim
import VizSimTCP (lineMessageInFlight)
import VizUtils

------------------------------------------------------------------------------
-- The vizualisation rendering
--
data MsgTag = RB | IB | EB | VT

data LeiosP2PSimVizConfig
  = LeiosP2PSimVizConfig
  { nodeMessageColor :: BlockHeader -> (Double, Double, Double)
  , ptclMessageColor :: LeiosMessage -> Maybe (MsgTag, (Double, Double, Double))
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
    Cairo.showText $
      "Blocks generated: "
        ++ intercalate
          ",  "
          [ printf "%s: %i (%.2f %s/s)" lbl n (perSec n) lbl
          | (n, lbl) <- [(rbs, "RB"), (ibs, "IB"), (ebs, "EB"), (votes, "Vote")]
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
              ((r, g, b) : _) -> do
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
              ((r, g, b) : _) -> do
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
            Cairo.rectangle (x - 8) (y - 8) 16 16
            Cairo.setSourceRGB r g b
            Cairo.fillPreserve
            Cairo.setSourceRGB 0 0 0
            Cairo.stroke
          LinkPointsWrap fromPos toPos fromPos' toPos' -> do
            let (msgTrailingEdge, _msgLeadingEdge) =
                  lineMessageInFlight now fromPos toPos msgforecast
                Point x y = toScreenPoint msgTrailingEdge
            Cairo.rectangle (x - 8) (y - 8) 16 16 -- TODO: use tag to pick different shape.
            Cairo.setSourceRGB r g b
            Cairo.fillPreserve
            Cairo.setSourceRGB 0 0 0
            Cairo.stroke
            let (msgTrailingEdge', _msgLeadingEdge) =
                  lineMessageInFlight now fromPos' toPos' msgforecast
                Point x' y' = toScreenPoint msgTrailingEdge'
            Cairo.rectangle (x' - 8) (y' - 8) 16 16
            Cairo.setSourceRGB r g b
            Cairo.fillPreserve
            Cairo.setSourceRGB 0 0 0
            Cairo.stroke
        | ((fromNode, toNode), msgs) <- Map.toList vizMsgsInTransit
        , (msg, msgforecast, _msgforecasts) <- msgs
        , now >= msgSendTrailingEdge msgforecast
        , now <= msgRecvTrailingEdge msgforecast
        , (tag, (r, g, b)) <- maybeToList (ptclMessageColor msg)
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
  [(msg, TcpMsgForecast, [TcpMsgForecast])] ->
  MsgsInFlightClassification
classifyInFlightMsgs [] = MsgsInFlightNone
classifyInFlightMsgs msgs
  | all control msgs = MsgsInFlightControl
  | all ballistic msgs = MsgsInFlightBallistic
  | otherwise = MsgsInFlightNonBallistic
 where
  -- We rely on contiguous forecast fragments having been merged,
  -- see mergeAdjacentForecasts
  ballistic (_msg, _msgforecast, _msgforecasts@[_]) = True
  ballistic _ = False

  -- We arbitrarily define a control message to be one that's less than a
  -- single TCP segment. All substantive payloads will be bigger than this.
  control (_msg, msgforecast, _msgforecasts) =
    msgSize msgforecast <= segmentSize

------------------------------------------------------------------------------
-- The charts
--

diffusionLatencyPerStakeFraction :: Int -> Time -> [Time] -> [(DiffTime, Double)]
diffusionLatencyPerStakeFraction nnodes created arrivals =
  [ (latency, percent)
  | (arrival, n) <- zip (reverse arrivals) [1 :: Int ..]
  , let !latency = arrival `diffTime` created
        !percent =
          (fromIntegral n / fromIntegral nnodes)
  ]

chartDiffusionLatency ::
  LeiosP2PSimVizConfig ->
  VizRender LeiosSimVizModel
chartDiffusionLatency LeiosP2PSimVizConfig{nodeMessageColor} =
  chartVizRender 25 $
    \_
     _
     ( SimVizModel
        _
        LeiosSimVizState
          { vizNodePos
          , vizMsgsDiffusionLatency
          }
      ) ->
        (Chart.def :: Chart.Layout DiffTime Chart.Percent)
          { Chart._layout_title = "Diffusion latency"
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
                      let (r, g, b) = nodeMessageColor blk
                       in Chart.def
                            { Chart._line_color = Chart.opaque (Colour.sRGB r g b)
                            }
                  }
              | let nnodes = Map.size vizNodePos
              , (blk, _nid, created, arrivals) <- Map.elems vizMsgsDiffusionLatency
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
        (\_ -> processingDelay)
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

-- | takes stage length, assumes pipelines start at Slot 0.
defaultVizConfig :: Int -> LeiosP2PSimVizConfig
defaultVizConfig stageLength =
  LeiosP2PSimVizConfig
    { nodeMessageColor = testNodeMessageColor
    , ptclMessageColor = testPtclMessageColor
    }
 where
  testPtclMessageColor ::
    LeiosMessage ->
    Maybe (MsgTag, (Double, Double, Double))
  testPtclMessageColor msg0 =
    case msg0 of
      PraosMsg msg ->
        (RB,) <$> case msg of
          PraosMessage (Right (ProtocolMessage (SomeMessage MsgBlock{}))) ->
            Just (praosMessageColor examplesLeiosSimVizConfig msg)
          _ -> Nothing
      RelayIB msg -> (IB,) <$> relayMessageColor (pipelineColor Propose . bimap hash (.slot)) msg
      RelayEB msg -> (EB,) <$> relayMessageColor (pipelineColor Endorse . bimap hash (.slot)) msg
      RelayVote msg -> (VT,) <$> relayMessageColor (pipelineColor Vote . bimap hash (.slot)) msg
  relayMessageColor :: ((id, body) -> (Double, Double, Double)) -> RelayMessage id header body -> Maybe (Double, Double, Double)
  relayMessageColor f (ProtocolMessage (SomeMessage msg)) = case msg of
    MsgRespondBodies bodies -> Just $ blendColors $ map f bodies
    _otherwise -> Nothing
  testNodeMessageColor :: BlockHeader -> (Double, Double, Double)
  testNodeMessageColor = blockHeaderColorAsBody
  paletteColor p seed = (r * f, g * f, b * f) -- this is also not how you adjust saturation.
   where
    -- TODO?: better palettes than gradients on a color
    palettes = [(0, 0, 1), (0, 1, 0), (1, 0.65, 0), (0.5, 0, 0.5)]
    (r, g, b) = palettes !! p
    f = fst $ uniformR (0.2, 1) seed
  pipelineColor :: Stage -> (Int, SlotNo) -> (Double, Double, Double)
  pipelineColor slotStage (i, slot) = case stageRange' stageLength slotStage slot Propose of
    Just (fromEnum -> startOfPipeline, _) ->
      let pipeline_idx = startOfPipeline `div` (4 * stageLength)
       in paletteColor (pipeline_idx `mod` 4) (mkStdGen i)
    Nothing -> (0, 0, 0)

-- might be ugly blending, but in practice it's going to be singleton lists?
blendColors :: [(Double, Double, Double)] -> (Double, Double, Double)
blendColors xs = coerce $ mconcat $ [(Sum (r * f), Sum (g * f), Sum (b * f)) | (r, g, b) <- xs]
 where
  f = 1 / fromIntegral (length xs)

example2 :: Visualization
example2 =
  slowmoVisualization 0.8 $
    Viz (leiosSimVizModel exampleTrace2) $
      LayoutAbove
        [ LayoutBeside [layoutLabelTime, Layout leiosGenCountRender]
        , LayoutBeside
            [ LayoutReqSize 1200 1000 $
                Layout $
                  leiosP2PSimVizRender config
            , LayoutBeside
                [ LayoutAbove
                    [ LayoutReqSize 350 300 $
                        Layout $
                          chartDiffusionLatency config
                          -- , LayoutReqSize 350 300 $
                          --     Layout $
                          --       chartDiffusionImperfection
                          --         p2pTopography
                          --         0.1
                          --         (96 / 1000)
                          --         config
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
