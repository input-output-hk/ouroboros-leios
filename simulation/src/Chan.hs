{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Chan (
  ConnectionConfig (..),
  newConnectionBundle,
  mkConnectionConfig,
  module Chan.Core,
  module Chan.Driver,
  module Chan.Mux,
  module Chan.TCP,
) where

import Chan.Core
import Chan.Driver
import Chan.Mux
import Chan.TCP
import Control.Concurrent.Class.MonadMVar (MonadMVar (..))
import Control.Monad.Class.MonadAsync (MonadAsync)
import Control.Monad.Class.MonadFork (MonadFork)
import Control.Tracer (Tracer)
import Data.Maybe (fromMaybe)
import ModelTCP (kilobytes, mkTcpConnProps)
import TimeCompat (DiffTime, MonadDelay, MonadMonotonicTimeNSec, MonadTime)

data ConnectionConfig = ConnectionConfig
  { transportConfig :: !TransportConfig
  , mux :: !Bool
  }

mkConnectionConfig :: Bool -> Bool -> DiffTime -> Maybe Bytes -> ConnectionConfig
mkConnectionConfig tcp mux tcpLatency maybeTcpBandwidth = ConnectionConfig{..}
 where
  transportConfig
    | tcp = TransportTcp (mkTcpConnProps tcpLatency (fromMaybe defaultTcpBandwidth maybeTcpBandwidth))
    | otherwise = TransportBasic
  defaultTcpBandwidth = (kilobytes 1000)

data TransportConfig
  = TransportBasic
  | TransportTcp !TcpConnProps

newConnectionBundle ::
  forall bundle m.
  (ConnectionBundle bundle, MonadTime m, MonadMonotonicTimeNSec m, MonadDelay m, MonadAsync m, MessageSize (BundleMsg bundle), MonadMVar m, MonadFork m) =>
  Tracer m (LabelTcpDir (TcpEvent (BundleMsg bundle))) ->
  ConnectionConfig ->
  m (bundle (Chan m), bundle (Chan m))
newConnectionBundle tracer = \case
  ConnectionConfig TransportBasic _mux@False -> undefined
  ConnectionConfig TransportBasic _mux@True -> undefined
  ConnectionConfig (TransportTcp _tcpConnProps) _mux@False -> undefined
  ConnectionConfig (TransportTcp tcpConnProps) _mux@True ->
    newConnectionBundleTCP tracer tcpConnProps
