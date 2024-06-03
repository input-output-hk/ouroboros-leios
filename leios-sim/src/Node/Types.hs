{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Node.Types where

initializeNode :: LeiosParameters -> IO Node
initializeNode params = undefined

data Node = Node

newtype NodeId = NodeId String
  deriving newtype (Ord, Eq, Show)

data LeiosParameters = LeiosParameters
data NodeState = NodeState
data EndorsementBlock = EndorsementBlock
