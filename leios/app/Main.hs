{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Leios.Node (Params (..), runSimulation)

main :: IO ()
main = runSimulation params
 where
  params =
    Params
      { λ = 12
      , capacity = 10
      , seed = 42
      , initialRound = 10
      }
