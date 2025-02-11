{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Chan (
  ConnectionConfig (..),
  newConnectionBundle,
  mkConnectionConfig,
  module Chan.Core,
  module Chan.Driver,
  -- Chan.Mux
  Bytes,
  ConnectionBundle (..),
  TcpConnProps (..),
  TcpEvent (..),
  LabelTcpDir (..),
  MessageSize (..),
  ToFromBundleMsg (..),
) where

import Chan.Core
import Chan.Driver
import Chan.Mux
import Chan.Simple (SimpleConnProps (..), newConnectionSimple)
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
    | otherwise = TransportSimple (SimpleConnProps tcpLatency maybeTcpBandwidth)
  defaultTcpBandwidth = (kilobytes 1000)

data TransportConfig
  = TransportSimple !SimpleConnProps
  | TransportTcp !TcpConnProps

newConnectionBundle ::
  forall bundle m.
  (ConnectionBundle bundle, MonadTime m, MonadMonotonicTimeNSec m, MonadDelay m, MonadAsync m, MessageSize (BundleMsg bundle), MonadMVar m, MonadFork m) =>
  Tracer m (LabelTcpDir (TcpEvent (BundleMsg bundle))) ->
  ConnectionConfig ->
  m (bundle (Chan m), bundle (Chan m))
newConnectionBundle tracer = \case
  ConnectionConfig (TransportSimple _simpleConnProps) _mux@False ->
    error "Unsupported configuration (no TCP, no mux)"
  ConnectionConfig (TransportSimple simpleConnProps) _mux@True -> do
    let tracer' = contramap ((fmap . fmap) fromBearerMsg) tracer
    (mA, mB) <- newConnectionSimple tracer' simpleConnProps
    (,) <$> newMuxChan mA <*> newMuxChan mB
  ConnectionConfig (TransportTcp _tcpConnProps) _mux@False ->
    error "Unsupported configuration (no mux)"
  ConnectionConfig (TransportTcp tcpConnProps) _mux@True -> do
    let tracer' = contramap ((fmap . fmap) fromBearerMsg) tracer
    (mA, mB) <- newConnectionTCP tracer' tcpConnProps
    (,) <$> newMuxChan mA <*> newMuxChan mB
