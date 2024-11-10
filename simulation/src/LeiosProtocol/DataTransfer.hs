{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module LeiosProtocol.DataTransfer where

import ChanDriver (ProtocolMessage)
import Control.Concurrent.Class.MonadSTM (MonadSTM)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Singletons (Sing, SingI (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word16, Word64)
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (..),
  Protocol (..),
  StateTokenI (..),
 )

import Control.Monad.Class.MonadTimer (MonadDelay)
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS

data BlockingStyle
  = StBlocking
  | StNonBlocking
  deriving (Show)

type SingBlockingStyle :: BlockingStyle -> Type
data SingBlockingStyle blocking where
  SingBlocking :: SingBlockingStyle StBlocking
  SingNonBlocking :: SingBlockingStyle StNonBlocking

deriving instance Show (SingBlockingStyle blocking)

type instance Sing @BlockingStyle = SingBlockingStyle

instance SingI StBlocking where sing = SingBlocking
instance SingI StNonBlocking where sing = SingNonBlocking

decideSingBlockingStyle ::
  SingBlockingStyle st ->
  SingBlockingStyle st' ->
  Maybe (st :~: st')
decideSingBlockingStyle SingBlocking SingBlocking = Just Refl
decideSingBlockingStyle SingNonBlocking SingNonBlocking = Just Refl
decideSingBlockingStyle _ _ = Nothing

type DataTransferState :: Type -> Type -> Type
data DataTransferState header body
  = StInit
  | StIdle
  | StHeaders BlockingStyle
  | StBodies
  | StDone

data SingDataTransferState (st :: DataTransferState header body) where
  SingStInit :: SingDataTransferState StInit
  SingStIdle :: SingDataTransferState StIdle
  SingStHeaders :: Sing blocking -> SingDataTransferState (StHeaders blocking)
  SingStBodies :: SingDataTransferState StBodies
  SingStDone :: SingDataTransferState StDone

decideSingDataTransferState ::
  SingDataTransferState st ->
  SingDataTransferState st' ->
  Maybe (st :~: st')
decideSingDataTransferState SingStInit SingStInit = Just Refl
decideSingDataTransferState SingStIdle SingStIdle = Just Refl
decideSingDataTransferState (SingStHeaders b1) (SingStHeaders b2) =
  fmap (\Refl -> Refl) (decideSingBlockingStyle b1 b2)
decideSingDataTransferState SingStBodies SingStBodies = Just Refl
decideSingDataTransferState SingStDone SingStDone = Just Refl
decideSingDataTransferState _ _ = Nothing

instance StateTokenI StInit where stateToken = SingStInit
instance StateTokenI StIdle where stateToken = SingStIdle
instance SingI blocking => StateTokenI (StHeaders blocking) where stateToken = SingStHeaders sing
instance StateTokenI StBodies where stateToken = SingStBodies
instance StateTokenI StDone where stateToken = SingStDone

decideDataTransferState ::
  forall (header :: Type) (body :: Type) (st :: DataTransferState header body) (st' :: DataTransferState header body).
  (StateTokenI st, StateTokenI st') =>
  Maybe (st :~: st')
decideDataTransferState = decideSingDataTransferState stateToken stateToken

newtype WindowShrink = WindowShrink Word16
  deriving (Show)

newtype WindowExpand = WindowExpand Word16
  deriving (Show)

newtype SizeInBytes = SizeInBytes Word64
  deriving (Show)

type BlockingReplyList :: BlockingStyle -> Type -> Type
data BlockingReplyList blocking a where
  BlockingReply :: NonEmpty a -> BlockingReplyList StBlocking a
  NonBlockingReply :: [a] -> BlockingReplyList StNonBlocking a

instance Protocol (DataTransferState header body) where
  data Message (DataTransferState header body) from to where
    MsgInit ::
      Message (DataTransferState header body) StInit StIdle
    MsgRequestHeaders ::
      SingBlockingStyle blocking ->
      WindowShrink ->
      WindowExpand ->
      Message (DataTransferState header body) StIdle (StHeaders blocking)
    MsgRespondHeaders ::
      BlockingReplyList blocking (header, SizeInBytes) ->
      Message (DataTransferState header body) (StHeaders blocking) StIdle
    MsgRequestBodies ::
      [header] ->
      Message (DataTransferState header body) StIdle StBodies
    MsgResponseBodies ::
      [body] ->
      Message (DataTransferState header body) StBodies StIdle
    MsgDone ::
      Message (DataTransferState header body) (StHeaders StBlocking) StDone

  type StateAgency StInit = ClientAgency
  type StateAgency StIdle = ServerAgency
  type StateAgency (StHeaders _blocking) = ClientAgency
  type StateAgency StBodies = ClientAgency
  type StateAgency StDone = NobodyAgency

  type StateToken = SingDataTransferState

deriving instance Show a => Show (BlockingReplyList blocking a)
deriving instance (Show header, Show body) => Show (Message (DataTransferState header body) from to)

dataTransferMessageLabel :: Message (DataTransferState header body) st st' -> String
dataTransferMessageLabel = \case
  MsgInit{} -> "MsgInit"
  MsgRequestHeaders{} -> "MsgRequestHeaders"
  MsgRespondHeaders{} -> "MsgRespondHeaders"
  MsgRequestBodies{} -> "MsgRequestBodies"
  MsgResponseBodies{} -> "MsgResponseBodies"
  MsgDone{} -> "MsgDone"

type DataTransferMessage header body = ProtocolMessage (DataTransferState header body)

--------------------------------
---- Data Producer
--------------------------------

data DataProducerState header body m = DataProducerState {}

type DataProducer header body st m a = TS.Server (DataTransferState header body) 'NonPipelined st m a

dataProducer ::
  forall header body m.
  (MonadSTM m, MonadDelay m) =>
  DataProducerState header body m ->
  DataProducer header body 'StIdle m ()
dataProducer = undefined

--------------------------------
---- Data Consumer
--------------------------------

data DataConsumerState header body m = DataConsumerState {}

type DataConsumer header body st m a = TC.Client (DataTransferState header body) 'NonPipelined st m a

dataConsumer ::
  forall header body m.
  (MonadSTM m, MonadDelay m) =>
  DataConsumerState header body m ->
  DataConsumer header body 'StIdle m ()
dataConsumer = undefined
