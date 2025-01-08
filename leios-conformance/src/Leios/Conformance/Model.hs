{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Leios.Conformance.Model where

import Data.Aeson (FromJSON, ToJSON)
import Data.Maybe (maybeToList)
import GHC.Generics (Generic)
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))

data EnvAction
  = Tick
  | NewIB InputBlock
  | NewEB EndorserBlock
  deriving (Eq, Show)

-- TODO: use InputBlock extracted from Agda
data InputBlock = InputBlock
  deriving (Show, Eq, Generic)

instance FromJSON InputBlock
instance ToJSON InputBlock
instance Pretty InputBlock where
  pPrint InputBlock = "InputBlock"

-- TODO: use EndorserBlock extracted from Agda
data EndorserBlock = EndorserBlock
  deriving (Show, Eq, Generic)

instance FromJSON EndorserBlock
instance ToJSON EndorserBlock
instance Pretty EndorserBlock where
  pPrint EndorserBlock = "EndorserBlock"

-- TODO: use LeiosState extracted from Agda
data NodeModel = NodeModel
  { slot :: Integer
  , ibs :: [InputBlock]
  , ebs :: [EndorserBlock]
  }
  deriving Show

initialModelState :: NodeModel
initialModelState = NodeModel 0 [] []

--TODO
makeIB :: NodeModel -> Maybe InputBlock
makeIB _ = Nothing

--TODO
makeEB :: NodeModel -> Maybe EndorserBlock
makeEB _ = Nothing

addIB :: InputBlock -> NodeModel -> NodeModel
addIB ib nm@NodeModel{..} = nm { ibs = ib : ibs }

addEB :: EndorserBlock -> NodeModel -> NodeModel
addEB eb nm@NodeModel{..} = nm { ebs = eb : ebs }

-- TODO: Leios executable specification
transition :: NodeModel -> EnvAction -> Maybe (([InputBlock], [EndorserBlock]), NodeModel)
transition nm Tick = do
  -- TODO: guards
  let ibs = maybeToList (makeIB nm)
      ebs = maybeToList (makeEB nm)
  pure ((ibs, ebs), nm)
transition nm (NewIB ib) = do
  -- TODO: guards
  pure (([], []), addIB ib nm)
transition nm (NewEB eb) = do
  -- TODO: guards
  pure (([], []), addEB eb nm)
