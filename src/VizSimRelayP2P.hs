{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module VizSimRelayP2P where

import           Data.Maybe
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import           Control.Monad.Class.MonadTime (Time, DiffTime, diffTime)

import qualified Graphics.Rendering.Cairo as Cairo
import qualified Graphics.Rendering.Chart.Easy as Chart
import qualified Data.Colour.SRGB as Colour

import ModelTCP (TcpMsgForecast(..), segmentSize)
import SimRelay (TestBlock, TestBlockRelayMessage)
import Viz
import VizChart
import VizSim
import VizSimTCP (lineMessageInFlight)
import VizSimRelay (RelaySimVizModel, RelaySimVizState(..), recentRate)


------------------------------------------------------------------------------
-- The vizualisation rendering
--

data RelayP2PSimVizConfig =
     RelayP2PSimVizConfig {
       nodeMessageColor :: TestBlock             -> (Double, Double, Double),
       ptclMessageColor :: TestBlockRelayMessage -> Maybe (Double, Double, Double)
     }

relayP2PSimVizRender :: RelayP2PSimVizConfig
                     -> (Int, Int)
                     -> VizRender RelaySimVizModel
relayP2PSimVizRender vizConfig renderReqSize =
    VizRender {
      renderReqSize,
      renderChanged = \_t _fn _m -> True,
      renderModel   = \ t _fn  m _ -> relayP2PSimVizRenderModel vizConfig t m
    }

relayP2PSimVizRenderModel :: RelayP2PSimVizConfig
                          -> Time
                          -> SimVizModel event RelaySimVizState
                          -> Cairo.Render ()
relayP2PSimVizRenderModel RelayP2PSimVizConfig {
                            nodeMessageColor,
                            ptclMessageColor
                          }
                          now
                          (SimVizModel _events
                             RelaySimVizState {
                               vizNodePos,
                               vizNodeLinks,
                               vizMsgsInTransit,
                               vizMsgsAtNodeQueue,
                               vizMsgsAtNodeBuffer,
--                               vizMsgsAtNodeRecentQueue,
--                               vizMsgsAtNodeRecentBuffer,
--                               vizMsgsAtNodeTotalQueue,
--                               vizMsgsAtNodeTotalBuffer,
                               vizNumMsgsGenerated
                             }) = do
    renderLinks
    renderNodes
    renderGenCount
  where
    renderGenCount = do
      Cairo.moveTo 5 40
      Cairo.setFontSize 20
      Cairo.setSourceRGB 0 0 0
      Cairo.showText $ "Blocks generated: " ++ show vizNumMsgsGenerated

    renderNodes = do
      Cairo.save
      Cairo.setFontSize 10
      sequence_
        [ do Cairo.arc x y 10 0 (pi * 2)
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

        | (node, (x,y)) <- Map.toList vizNodePos
        , let qmsgs   = fromMaybe [] (Map.lookup node vizMsgsAtNodeQueue)
              bmsgs   = fromMaybe [] (Map.lookup node vizMsgsAtNodeBuffer)
--              nqmsgs  = length qmsgs
--              nbmsgs  = length bmsgs
              (r,g,b) = case qmsgs ++ bmsgs of
                          msgs@(_:_) -> nodeMessageColor (last msgs)
                          _          -> (0.7,0.7,0.7)
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
            MsgsInFlightNonBalistic ->
              case catMaybes [ ptclMessageColor msg | (msg,_,_) <-  msgs ] of
                [] -> return ()
                ((r,g,b):_) -> do
                  uncurry Cairo.moveTo fromPos
                  uncurry Cairo.lineTo toPos
                  Cairo.setSourceRGB r g b
                  Cairo.setLineWidth 1
                  Cairo.setDash [10,5] 0
                  Cairo.stroke

            -- We draw with a full line
            MsgsInFlightBalistic ->
              case catMaybes [ ptclMessageColor msg | (msg,_,_) <-  msgs ] of
                [] -> return ()
                ((r,g,b):_) -> do
                  uncurry Cairo.moveTo fromPos
                  uncurry Cairo.lineTo toPos
                  Cairo.setSourceRGB r g b
                  Cairo.setDash [] 0
                  Cairo.setLineWidth 2
                  Cairo.stroke

        | (fromPos, toPos, msgs) <- linksAndMsgs
        ]
      Cairo.restore
      -- draw the messages in flight on top
      sequence_
        [ do Cairo.rectangle (x-8) (y-8) 16 16
             Cairo.setSourceRGB r g b
             Cairo.fillPreserve
             Cairo.setSourceRGB 0 0 0
             Cairo.stroke
        | (fromPos, toPos, msgs) <- linksAndMsgs
        , (msg, msgforecast, _msgforecasts) <- msgs
        , now >= msgSendTrailingEdge msgforecast
        , now <= msgRecvTrailingEdge msgforecast
        , (r,g,b) <- maybeToList (ptclMessageColor msg)
        , let (_msgTrailingEdge@(x,y), _msgLeadingEdge) =
                lineMessageInFlight now fromPos toPos msgforecast
        ]
      Cairo.restore
      where
        linksAndMsgs =
          [ (fromPos, toPos, msgs)
          | (fromNode, toNode) <- Set.toList vizNodeLinks
          , let (fromPos, toPos) = (vizNodePos Map.! fromNode,
                                    vizNodePos Map.! toNode)
                msgs = Map.findWithDefault
                         [] (fromNode, toNode)
                         vizMsgsInTransit
          ]

data MsgsInFlightClassification =
       MsgsInFlightNone
     | MsgsInFlightControl
     | MsgsInFlightNonBalistic
     | MsgsInFlightBalistic

classifyInFlightMsgs :: [(msg, TcpMsgForecast, [TcpMsgForecast])]
                     -> MsgsInFlightClassification
classifyInFlightMsgs []   = MsgsInFlightNone
classifyInFlightMsgs msgs
  | all control msgs      = MsgsInFlightControl
  | all balistic msgs     = MsgsInFlightBalistic
  | otherwise             = MsgsInFlightNonBalistic
  where
    -- We rely on contiguous forecast fragments having been merged,
    -- see mergeAdjacentForecasts
    balistic (_msg, _msgforecast, _msgforecasts@[_]) = True
    balistic _                                       = False

    -- We arbitrarily define a control message to be one that's less than a
    -- single TCP segment. All substantive payloads will be bigger than this.
    control (_msg, msgforecast, _msgforecasts) =
      msgSize msgforecast <= segmentSize

------------------------------------------------------------------------------
-- The charts
--

chartDiffusionLatency :: RelayP2PSimVizConfig
                      -> VizRender RelaySimVizModel
chartDiffusionLatency RelayP2PSimVizConfig {nodeMessageColor} =
    chartVizRender 25 $ \_ _
      (SimVizModel _ RelaySimVizState {
                       vizNodePos,
                       vizMsgsDiffusionLatency
                     }) ->
      (Chart.def :: Chart.Layout DiffTime Chart.Percent) {
        Chart._layout_title = "Diffusion latency: time to reach fraction of stake"
      , Chart._layout_y_axis =
          (Chart.def :: Chart.LayoutAxis Chart.Percent) {
            Chart._laxis_generate =
              Chart.scaledAxis Chart.def { Chart._la_nLabels = 10 } (0, 1)
          }
      , Chart._layout_plots =
          [ Chart.toPlot $
              Chart.def {
                Chart._plot_lines_values = [timeseries]
              , Chart._plot_lines_style =
                  let (r,g,b) = nodeMessageColor blk
                  in Chart.def {
                       Chart._line_color = Chart.opaque (Colour.sRGB r g b)
                     }
              }
          | let nnodes = Map.size vizNodePos
          , (blk, created, arrivals) <- Map.elems vizMsgsDiffusionLatency
          , let timeseries =
                  [ (latency, percent)
                  | (arrival, n) <- zip (reverse arrivals) [1 :: Int ..]
                  , let !latency = arrival `diffTime` created
                        !percent = Chart.Percent
                                     (fromIntegral n / fromIntegral nnodes)
                  ]
          ]
      }

chartBandwidthInbound :: VizRender RelaySimVizModel
chartBandwidthInbound =
    chartVizRender 25 $ \_ _
      (SimVizModel _ RelaySimVizState {
                       vizMsgsAtNodeRecentQueue
                     }) ->
      (Chart.def :: Chart.Layout Double Double) {
        Chart._layout_title  = "Distribution of frequency of block arrival"
      , Chart._layout_x_axis =
          Chart.def {
            Chart._laxis_generate =
              Chart.scaledAxis Chart.def { Chart._la_nLabels = maxX } (0, maxX)
          }
      , Chart._layout_y_axis =
          Chart.def {
            Chart._laxis_generate =
              Chart.scaledAxis Chart.def { Chart._la_nLabels = 5 } (0, 0.5)
          }
      , Chart._layout_plots =
          [ Chart.histToPlot $
            Chart.defaultNormedPlotHist {
              Chart._plot_hist_values =
                map ((fromIntegral :: Int -> Double) . recentRate)
                    (Map.elems vizMsgsAtNodeRecentQueue)
            , Chart._plot_hist_range = Just (0, maxX)
            , Chart._plot_hist_bins  = maxX
            }
          | not (Map.null vizMsgsAtNodeRecentQueue)
          ]
      }
  where
    maxX :: Num a => a
    maxX = 15

chartBandwidthCPU :: VizRender RelaySimVizModel
chartBandwidthCPU =
    chartVizRender 25 $ \_ _
      (SimVizModel _ RelaySimVizState {
                       vizMsgsAtNodeRecentBuffer
                     }) ->
      (Chart.def :: Chart.Layout Double Double) {
        Chart._layout_title  = "Distribution of frequency of block processing"
      , Chart._layout_x_axis =
          Chart.def {
            Chart._laxis_generate =
              Chart.scaledAxis Chart.def { Chart._la_nLabels = maxX } (0, maxX)
          }
      , Chart._layout_y_axis =
          Chart.def {
            Chart._laxis_generate =
              Chart.scaledAxis Chart.def { Chart._la_nLabels = 5 } (0, 0.5)
          }
      , Chart._layout_plots =
          [ Chart.histToPlot $
            Chart.defaultNormedPlotHist {
              Chart._plot_hist_values =
                map ((fromIntegral :: Int -> Double) . recentRate)
                    (Map.elems vizMsgsAtNodeRecentBuffer)
            , Chart._plot_hist_range = Just (0, maxX)
            , Chart._plot_hist_bins  = maxX
            }
          | not (Map.null vizMsgsAtNodeRecentBuffer)
          ]
      }
  where
    maxX :: Num a => a
    maxX = 15

