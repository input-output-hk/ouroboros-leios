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
import Control.Tracer (Contravariant (contramap), Tracer)
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
  ConnectionConfig TransportBasic _mux@False ->
    error "Unsupported configuration (no TCP, no mux)"
  ConnectionConfig TransportBasic _mux@True ->
    error "Unsupported configuration (no TCP)"
  ConnectionConfig (TransportTcp _tcpConnProps) _mux@False ->
    error "Unsupported configuration (no mux)"
  ConnectionConfig (TransportTcp tcpConnProps) _mux@True ->
    newConnectionBundleTCPMux tracer tcpConnProps

newConnectionBundleTCPMux ::
  forall bundle m.
  (ConnectionBundle bundle, MonadTime m, MonadMonotonicTimeNSec m, MonadDelay m, MonadAsync m, MessageSize (BundleMsg bundle), MonadMVar m, MonadFork m) =>
  Tracer m (LabelTcpDir (TcpEvent (BundleMsg bundle))) ->
  TcpConnProps ->
  m (bundle (Chan m), bundle (Chan m))
newConnectionBundleTCPMux tracer tcpprops = do
  let tracer' = contramap ((fmap . fmap) fromBearerMsg) tracer
  (mA, mB) <- newConnectionTCP tracer' tcpprops
  (,) <$> newMuxChan mA <*> newMuxChan mB
