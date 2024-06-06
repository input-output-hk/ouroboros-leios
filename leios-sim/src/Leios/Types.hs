module Leios.Types  where

  type Coin = Int

  type SlotNumber = Int

  data Params = Params {
    noOfParties  :: Int
    , l          :: Int
    , lambda     :: Int
    , mu         :: Int
    , ibFreq     :: Int
    , ebFreq     :: Int
    , totalStake :: Coin
    , randomSeed :: Int
  }
