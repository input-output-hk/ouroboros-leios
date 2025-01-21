{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module ChanDriver where

import Chan
import ChanTCP
import Data.Type.Equality
import Network.TypedProtocol (
  ActiveState,
  Driver (..),
  Protocol (Message),
  SomeMessage (..),
  StateTokenI,
  TheyHaveAgencyProof,
  WeHaveAgencyProof,
 )

data ProtocolMessage ps where
  ProtocolMessage ::
    forall ps (st :: ps).
    SomeMessage st ->
    ProtocolMessage ps

instance forall ps. (forall st st'. Show (Message ps st st')) => Show (ProtocolMessage ps) where
  show (ProtocolMessage (SomeMessage msg)) = show msg

instance forall ps. (forall st st'. MessageSize (Message ps st st')) => MessageSize (ProtocolMessage ps) where
  messageSizeBytes (ProtocolMessage (SomeMessage msg)) = messageSizeBytes msg

type CompareStateToken ps = forall (st :: ps) (st' :: ps). (StateTokenI st, StateTokenI st') => Maybe (st :~: st')

chanDriver ::
  forall ps pr m.
  Monad m =>
  CompareStateToken ps ->
  Chan m (ProtocolMessage ps) ->
  Driver ps pr () m
chanDriver cmp ch =
  Driver
    { sendMessage = sendMessage
    , recvMessage = recvMessage
    , initialDState = ()
    }
 where
  sendMessage ::
    forall (st :: ps) (st' :: ps).
    (StateTokenI st, StateTokenI st', ActiveState st) =>
    WeHaveAgencyProof pr st ->
    Message ps st st' ->
    m ()
  sendMessage _prf msg =
    writeChan ch (ProtocolMessage (SomeMessage msg))

  recvMessage ::
    forall (st :: ps).
    (StateTokenI st, ActiveState st) =>
    TheyHaveAgencyProof pr st ->
    () ->
    m (SomeMessage st, ())
  recvMessage _prf () = do
    ProtocolMessage smsg <- readChan ch
    case smsg of
      SomeMessage @_ @st' msg -> case cmp @st @st' of
        Just Refl -> pure (SomeMessage msg, ())
        Nothing -> error "recvMessage: read message state does not match expected state"
