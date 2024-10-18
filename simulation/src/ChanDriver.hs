{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module ChanDriver where

import Chan
import ChanTCP
import Data.Type.Equality
import Network.TypedProtocol

data ProtocolMessage ps where
  ProtocolMessage :: forall ps (st :: ps). SomeMessage st -> ProtocolMessage ps

instance Show (ProtocolMessage ps) where
  show _ = "TODO"

instance forall ps. (forall st st'. MessageSize (Message ps st st')) => MessageSize (ProtocolMessage ps) where
  messageSizeBytes (ProtocolMessage (SomeMessage msg)) = messageSizeBytes msg

type CompareStateToken ps = forall (st :: ps) (st' :: ps). (StateTokenI st, StateTokenI st') => Maybe (st :~: st')

chanDriver :: forall ps pr m. Monad m => CompareStateToken ps -> Chan m (ProtocolMessage ps) -> Driver ps pr () m
chanDriver cmp ch =
  Driver
    { sendMessage = \_ msg -> writeChan ch (ProtocolMessage (SomeMessage msg))
    , recvMessage = recvMessage
    , initialDState = ()
    }
 where
  recvMessage ::
    forall (st :: ps).
    (StateTokenI st, ActiveState st) =>
    TheyHaveAgencyProof pr st ->
    () ->
    m (SomeMessage st, ())
  recvMessage _ _ = do
    ProtocolMessage smsg <- readChan ch
    case smsg of
      SomeMessage @_ @st1 @st' msg -> case cmp @st @st1 of
        Just Refl -> pure (SomeMessage msg, ())
        Nothing -> error "TODO"
