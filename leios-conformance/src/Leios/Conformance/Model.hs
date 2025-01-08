{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Leios.Conformance.Model where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))

type Chain = String
type Vote = String

data EnvAction
  = Tick
  | NewIB InputBlock
  | NewEB EndorserBlock
  deriving (Eq, Show)

data InputBlock = InputBlock
  deriving (Show, Eq, Generic)

instance FromJSON InputBlock
instance ToJSON InputBlock
instance Pretty InputBlock where
  pPrint InputBlock = "InputBlock"

data EndorserBlock = EndorserBlock
  deriving (Show, Eq, Generic)

instance FromJSON EndorserBlock
instance ToJSON EndorserBlock
instance Pretty EndorserBlock where
  pPrint EndorserBlock = "EndorserBlock"

-- TODO: LeiosState
data NodeModel = NodeModel
  { slot :: Integer
  , ibs :: [InputBlock]
  , ebs :: [EndorserBlock]
  }
  deriving Show

initialModelState :: NodeModel
initialModelState = NodeModel 0 [] []

-- TODO: Leios executable specification
transition :: NodeModel -> EnvAction -> Maybe (([InputBlock], [EndorserBlock]), NodeModel)
transition nm Tick = Just (([], []), nm)
transition nm (NewIB _) = Just (([], []), nm)
transition nm (NewEB _) = Just (([], []), nm)
