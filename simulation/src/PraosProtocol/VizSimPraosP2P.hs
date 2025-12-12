{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}

module PraosProtocol.VizSimPraosP2P where

import Data.Array.Unboxed (Ix, UArray, accumArray, (!))
import qualified Data.Colour.SRGB as Colour
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, maybeToList)
import qualified Graphics.Rendering.Cairo as Cairo
import qualified Graphics.Rendering.Chart.Easy as Chart
import TimeCompat

import Data.Bifunctor (second)
import ModelTCP (TcpMsgForecast (..), segmentSize)
import P2P
import PraosProtocol.Common (BlockBody, BlockHeader, FullTip (FullTip))
import PraosProtocol.PraosNode
import PraosProtocol.VizSimPraos (
  LinkPoints (..),
  PraosSimVizModel,
  PraosSimVizState (..),
  recentRate,
 )
import SimTypes (Point (..), World (..))
import Text.Printf (printf)
import Viz
import VizChart
import VizSim
import VizSimTCP (lineMessageInFlight)
import VizUtils

------------------------------------------------------------------------------
-- The vizualisation rendering
--

data PraosP2PSimVizConfig = PraosP2PSimVizConfig
  { nodeMessageColor :: BlockHeader -> (Double, Double, Double)
  , ptclMessageColor :: PraosMessage BlockBody -> Maybe (Double, Double, Double)
  }

praosP2PSimVizRender ::
  PraosP2PSimVizConfig ->
  VizRender PraosSimVizModel
praosP2PSimVizRender vizConfig =
  VizRender
    { renderReqSize = (500, 500) -- nominal, should be overridden
    , renderChanged = \_t _fn _m -> True
    , renderModel = \t _fn m sz ->
        praosP2PSimVizRenderModel vizConfig t m sz
    }

praosP2PSimVizRenderModel ::
  PraosP2PSimVizConfig ->
  Time ->
  SimVizModel event PraosSimVizState ->
  (Double, Double) ->
  Cairo.Render ()
praosP2PSimVizRenderModel
  PraosP2PSimVizConfig
    { nodeMessageColor
    , ptclMessageColor
    }
  now@(Time t)
  ( SimVizModel
      _events
      PraosSimVizState
        { vizWorld = World{worldDimensions}
        , vizNodePos
        , vizNodeLinks
        , vizNodeTip
        , vizMsgsInTransit
        , vizNumMsgsGenerated
        }
    )
  screenSize = do
    renderLinks
    renderNodes
    renderGenCount
   where
    renderGenCount = do
      Cairo.moveTo 5 40
      Cairo.setFontSize 20
      Cairo.setSourceRGB 0 0 0
      Cairo.showText $
        "Blocks generated: "
          ++ show vizNumMsgsGenerated
          ++ printf " (%.2f blk/s)" (fromIntegral vizNumMsgsGenerated / realToFrac t :: Double)

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
              case catMaybes [ptclMessageColor msg | (msg, _, _) <- msgs] of
                [] -> return ()
                ((r, g, b) : _) -> do
                  Cairo.setSourceRGB r g b
                  Cairo.setLineWidth 1
                  Cairo.setDash [10, 5] 0
                  case vizNodeLinks !!! (fromNode, toNode) of
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
              case catMaybes [ptclMessageColor msg | (msg, _, _) <- msgs] of
                [] -> return ()
                ((r, g, b) : _) -> do
                  Cairo.setSourceRGB r g b
                  Cairo.setDash [] 0
                  Cairo.setLineWidth 2
                  case vizNodeLinks !!! (fromNode, toNode) of
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
        [ case vizNodeLinks !!! (fromNode, toNode) of
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
              Cairo.rectangle (x - 8) (y - 8) 16 16
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
        , (r, g, b) <- maybeToList (ptclMessageColor msg)
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
        !percent = fromIntegral n / fromIntegral nnodes
  ]

chartDiffusionLatency ::
  PraosP2PSimVizConfig ->
  VizRender PraosSimVizModel
chartDiffusionLatency PraosP2PSimVizConfig{nodeMessageColor} =
  chartVizRender 25 $
    \_
     _
     ( SimVizModel
         _
         PraosSimVizState
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
  PraosP2PSimVizConfig ->
  VizRender PraosSimVizModel
chartDiffusionImperfection
  p2ptopography
  processingDelay
  serialisationDelay
  PraosP2PSimVizConfig{nodeMessageColor}
    | Map.size (p2pNodes p2ptopography) > 100 =
        nullVizRender
    | otherwise =
        chartVizRender 25 $
          \_
           _
           (SimVizModel _ PraosSimVizState{vizMsgsDiffusionLatency}) ->
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
        0
        processingDelay
        (\_ _ linkLatency -> 3 * linkLatency + serialisationDelay)

chartBandwidth :: VizRender PraosSimVizModel
chartBandwidth =
  chartVizRender 25 $
    \_
     _
     ( SimVizModel
         _
         PraosSimVizState
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

chartLinkUtilisation :: VizRender PraosSimVizModel
chartLinkUtilisation =
  chartVizRender 25 $
    \_
     _
     ( SimVizModel
         _
         PraosSimVizState
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
