{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

--TODO: share the orphans
{-# OPTIONS_GHC -Wno-orphans #-}

module PlotTCP where

import Control.Monad.Class.MonadTime

import Graphics.Gnuplot.Simple as Gnuplot
import qualified Graphics.Gnuplot.Value.Tuple as Gnuplot.Tuple
--import qualified Graphics.Gnuplot.Terminal.PNG as Gnuplot.PNG

import ModelTCP
import SimTCPLinks

------------------------------------------------------------------------------
-- Plotting
--

data DataSentOrReceived = DataSent | DataRecv
data ByMessageOrSegment = ByMessage | BySegment

tcpDataSeries :: ByMessageOrSegment -> DataSentOrReceived
              -> [TcpEvent a] -> [Maybe (DiffTime, Bytes)]
tcpDataSeries ByMessage DataSent = toDataSeries . selectSends . selectByMessage
tcpDataSeries ByMessage DataRecv = toDataSeries . selectRecvs . selectByMessage
tcpDataSeries BySegment DataSent = toDataSeries . selectSends . selectBySegment
tcpDataSeries BySegment DataRecv = toDataSeries . selectRecvs . selectBySegment

selectByMessage, selectBySegment :: [TcpEvent a] -> [TcpMsgForecast]
selectByMessage events = [ msgforecast
                         | TcpSendMsg _ msgforecast _ <- events ]
selectBySegment events = [ msgfragforecast
                         | TcpSendMsg _ _ msgfragforecasts <- events
                         , msgfragforecast <- msgfragforecasts ]

selectSends, selectRecvs :: [TcpMsgForecast] -> [(Time, Time, Bytes)]
selectSends forecasts = [ ( msgSendLeadingEdge  msgforecast
                          , msgSendTrailingEdge msgforecast
                          , msgSize             msgforecast
                          )
                        | msgforecast <- forecasts ]
selectRecvs forecasts = [ ( msgRecvLeadingEdge  msgforecast
                          , msgRecvTrailingEdge msgforecast
                          , msgSize             msgforecast
                          )
                        | msgforecast <- forecasts ]

toDataSeries :: [(Time, Time, Bytes)] -> [Maybe (DiffTime, Bytes)]
toDataSeries = go 0 0
  where
    go !_ !_  [] = []
    go !a !x0 ((Time x1, Time x2, dy) : ts)
      | x1 == x0  =           Just (x1, a) : Just (x2, a+dy) : go (a+dy) x2 ts
      | x1 >  x0  = Nothing : Just (x1, a) : Just (x2, a+dy) : go (a+dy) x2 ts
      | otherwise = error "toDataSeries: non-monotonic x values"

selectTcpLinkTrace :: NodeId -> NodeId
                   -> [(Time, TcpSimEvent)]
                   -> [TcpEvent TestMessage]
selectTcpLinkTrace a b t =
  [ e | (_, TcpSimEventTcp (LabelLink a' b' e)) <- t, a == a', b == b' ]

plotTrace :: ByMessageOrSegment -> [TcpEvent a] -> IO ()
plotTrace bymessageorsegment trace =
    Gnuplot.plotListsStyle
      [ Title   "Cumulative bytes sent by TCP transmission"
      , XLabel ("time in seconds")
      , YLabel ("bytes transmitted (cumulative)")
      , Key (Just ["top left"])
      , Grid (Just ["xtics", "ytics"])
--      , PNG "tcpplot.png"
      ]
      [ ( PlotStyle { plotType = LinesPoints
                    , lineSpec = CustomStyle [LineTitle "bytes sent"]}
        , tcpDataSeries bymessageorsegment DataSent trace )
      , ( PlotStyle { plotType = LinesPoints
                    , lineSpec = CustomStyle [LineTitle "bytes received"]}
        , tcpDataSeries bymessageorsegment DataRecv trace )
      ]

instance Gnuplot.Tuple.C Bytes where
  text (Bytes b) = Gnuplot.Tuple.text b

instance Gnuplot.Tuple.C DiffTime where
  text = Gnuplot.Tuple.text . (realToFrac :: DiffTime -> Double)

instance Gnuplot.Tuple.C a => Gnuplot.Tuple.C (Maybe a) where
  text Nothing  = []
  text (Just x) = Gnuplot.Tuple.text x

  columnCount =
    case (Gnuplot.Tuple.columnCount :: Gnuplot.Tuple.ColumnCount a) of
      Gnuplot.Tuple.ColumnCount x -> Gnuplot.Tuple.ColumnCount x

------------------------------------------------------------------------------
-- Example plots
--

example1 :: IO ()
example1 =
    plotTrace BySegment $
      ModelTCP.traceTcpSend tcpprops trafficPattern
  where
    tcpprops       = mkTcpConnProps 0.3 (kilobytes 1000)
    trafficPattern = replicate 20 (kilobytes 100)


example2 :: IO ()
example2 =
    plotTrace ByMessage $
      selectTcpLinkTrace (NodeId 0) (NodeId 1) $
      SimTCPLinks.traceTcpLinks1 tcpprops trafficPattern
  where
    tcpprops       = mkTcpConnProps 0.3 (kilobytes 1000)
    trafficPattern = mkUniformTrafficPattern 20 (kilobytes 100) 0


