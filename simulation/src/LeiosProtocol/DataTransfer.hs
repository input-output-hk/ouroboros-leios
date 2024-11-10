module LeiosProtocol.DataTransfer where

import Data.Singletons (Sing, SingI (..))
import Data.Type.Equality ((:~:) (Refl))
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (NonPipelined),
  Protocol (..),
  StateTokenI (..),
  runPeerWithDriver,
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS

data BlockingStyle
  = StBlocking
  | StNonBlocking

data SingBlockingStyle (blocking :: BlockingStyle) where
  SingBlocking :: SingBlockingStyle StBlocking
  SingNonBlocking :: SingBlockingStyle StNonBlocking

type instance Sing @BlockingStyle = SingBlockingStyle
instance SingI StBlocking where sing = SingBlocking
instance SingI SingNonBlocking where sing = SingNonBlocking

decideSingBlockingStyle ::
  SingBlockingStyle st ->
  SingBlockingStyle st' ->
  Maybe (st :~: st')
decideSingBlockingStyle SingBlocking SingBlocking = Just Refl
decideSingBlockingStyle SingNonBlocking SingNonBlocking = Just Refl
decideSingBlockingStyle _ _ = Nothing

data DataTransferState header body
  = StInit
  | StIdle
  | StHeaders BlockingStyle
  | StBodies
  | StDone

data SingDataTransferState header body where
  SingStInit :: SingDataTransferState StInit
  SingStIdle :: SingDataTransferState StIdle
  SingStHeaders :: SingDataTransferState StHeaders
  SingStBodies :: SingDataTransferState StBodies
  SingStDone :: SingDataTransferState StDone

decideSingDataTransferState ::
  SingDataTransferState st ->
  SingDataTransferState st' ->
  Maybe (st :~: st')
decideSingDataTransferState SingStInit SingStInit = Just Refl
decideSingDataTransferState SingStIdle SingStIdle = Just Refl
decideSingDataTransferState SingStHeaders SingStHeaders = Just Refl
decideSingDataTransferState SingStBodies SingStBodies = Just Refl
decideSingDataTransferState SingStDone SingStDone = Just Refl
decideSingDataTransferState _ _ = Nothing

decideDataTransferState ::
  forall (st :: DataTransferState header body) (st' :: DataTransferState header body).
  (StateTokenI st, StateTokenI st') =>
  Maybe (st :~: st')
decideDataTransferState = decideSingDataTransferState stateToken stateToken

newtype WindowShrink = WindowShrink Word16

newtype WindowExpand = WindowExpand Word16

newtype SizeInBytes = SizeInBytes Word64

data BlockingReplyList (blocking :: BlockingStyle) a where
  BlockingReply :: NonEmpty a -> BlockingReplyList StBlocking
  NonBlockingReply :: [a] -> BlockingReplyList StNonBlocking

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
  type StateAgency StHeaders = ClientAgency
  type StateAgency StBodies = ClientAgency
  type StateAgency StDone = NobodyAgency

  type StateToken = SingDataTransferState

instance StateTokenI StInit where stateToken = SingStInit
instance StateTokenI StIdle where stateToken = SingStIdle
instance SingI blocking => StateTokenI (StHeaders blocking) where stateToken = SingStHeaders sing
instance StateTokenI StBodies where stateToken = SingStBodies
instance StateTokenI StDone where stateToken = SingStDone
