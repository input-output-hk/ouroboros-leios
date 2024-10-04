{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
module PraosProtocol where

import Network.TypedProtocol

--------------------------------
--- Common types
--------------------------------

-- TODO
data SlotNo
data BlockId
data BlockHeader
data ChainTip

data Point = Point BlockId SlotNo



--------------------------------
---- ChainSync
--------------------------------

data ChainSyncState
  = StIdle
  | StCanAwait
  | StMustReply
  | StIntersect
  | StDone

data SingChainSyncState (st :: ChainSyncState) where
  SingStIdle :: SingChainSyncState StIdle
  SingStCanAwait :: SingChainSyncState StCanAwait
  SingStMustReply :: SingChainSyncState StMustReply
  SingStIntersect :: SingChainSyncState StIntersect
  SingStDone :: SingChainSyncState StDone

instance Protocol ChainSyncState where
  data Message ChainSyncState from to where
    MsgRequestNext       ::
      BlockHeader ->
      ChainTip ->
      Message ChainSyncState StIdle StCanAwait
    MsgAwaitReply        :: Message ChainSyncState StCanAwait StMustReply
    MsgRollForward       :: Message ChainSyncState StCanAwait StIdle
    MsgRollBackward      ::
      Point ->
      ChainTip ->
      Message ChainSyncState StCanAwait StIdle
    MsgFindIntersect     ::
      [Point] ->
      Message ChainSyncState StIdle StIntersect
    MsgIntersectNotFound ::
      ChainTip ->
      Message ChainSyncState StIntersect StIdle
    MsgIntersectFound    ::
      Point ->
      ChainTip ->
      Message ChainSyncState StIntersect StIdle
    MsgDone              :: Message ChainSyncState StIdle StDone
  type StateAgency StIdle = ClientAgency
  type StateAgency StCanAwait = ServerAgency
  type StateAgency StMustReply = ServerAgency
  type StateAgency StIntersect = ServerAgency
  type StateAgency StDone = NobodyAgency

  type StateToken = SingChainSyncState

instance StateTokenI StIdle where stateToken = SingStIdle
instance StateTokenI StCanAwait where stateToken = SingStCanAwait
instance StateTokenI StMustReply where stateToken = SingStMustReply
instance StateTokenI StIntersect where stateToken = SingStIntersect
instance StateTokenI StDone where stateToken = SingStDone
