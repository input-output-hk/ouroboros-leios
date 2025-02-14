{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

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
import GHC.Generics
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
  (ConnectionBundle bundle, MonadTime m, MonadMonotonicTimeNSec m, MonadDelay m, MonadAsync m, MessageSize (BundleMsg bundle), BundleConstraint bundle ~ MessageSize, MonadMVar m, MonadFork m) =>
  Tracer m (LabelTcpDir (TcpEvent (BundleMsg bundle))) ->
  ConnectionConfig ->
  m (bundle (Chan m), bundle (Chan m))
newConnectionBundle tracer = \case
  ConnectionConfig (TransportSimple simpleConnProps) _mux@False -> do
    newUnMuxedConnectionBundle $ \tofrom ->
      newConnectionSimple (traceAsBundleMsg @bundle tofrom tracer) simpleConnProps
  ConnectionConfig (TransportSimple simpleConnProps) _mux@True -> do
    let tracer' = contramap ((fmap . fmap) fromBearerMsg) tracer
    (mA, mB) <- newConnectionSimple tracer' simpleConnProps
    (,) <$> newMuxChan mA <*> newMuxChan mB
  ConnectionConfig (TransportTcp tcpConnProps) _mux@False ->
    newUnMuxedConnectionBundle $ \tofrom ->
      newConnectionTCP (traceAsBundleMsg @bundle tofrom tracer) tcpConnProps
  ConnectionConfig (TransportTcp tcpConnProps) _mux@True -> do
    let tracer' = contramap ((fmap . fmap) fromBearerMsg) tracer
    (mA, mB) <- newConnectionTCP tracer' tcpConnProps
    (,) <$> newMuxChan mA <*> newMuxChan mB

newUnMuxedConnectionBundle ::
  forall bundle m.
  (Monad m, ConnectionBundle bundle, BundleConstraint bundle ~ MessageSize) =>
  (forall a. MessageSize a => ToFromBundleMsg (BundleMsg bundle) a -> m (Chan m a, Chan m a)) ->
  m (bundle (Chan m), bundle (Chan m))
newUnMuxedConnectionBundle newConn = do
  bundleOfConns <-
    traverseConnectionBundle @bundle @m
      (\tofrom -> (\(x, y) -> x :*: y) <$> newConn tofrom)
      toFromBundleMsgBundle
  (,)
    <$> traverseConnectionBundle @bundle @m (\(x :*: _) -> pure x) bundleOfConns
    <*> traverseConnectionBundle @bundle @m (\(_ :*: y) -> pure y) bundleOfConns

traceAsBundleMsg ::
  forall bundle m a.
  ToFromBundleMsg (BundleMsg bundle) a ->
  Tracer m (LabelTcpDir (TcpEvent (BundleMsg bundle))) ->
  Tracer m (LabelTcpDir (TcpEvent a))
traceAsBundleMsg ToFromBundleMsg{..} = (contramap . fmap . fmap) toBundleMsg
