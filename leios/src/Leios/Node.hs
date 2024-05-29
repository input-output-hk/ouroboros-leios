{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Basic simulation of a single Leios node.
module Leios.Node where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM,
  TQueue,
  atomically,
  flushTQueue,
  newTQueueIO,
  readTQueue,
  writeTQueue,
 )
import Control.Monad (forM_, forever)
import Control.Monad.Class.MonadAsync (MonadAsync, race)
import Control.Monad.Class.MonadSay (MonadSay, say)
import Control.Monad.Class.MonadTimer (MonadDelay, threadDelay)
import Control.Monad.IOSim (Trace)
import Control.Tracer (Tracer, traceWith)
import Data.Aeson (Value, toJSON)
import qualified Data.Aeson as A
import qualified Data.ByteString as BS
import Data.Bytes (Bytes (..))
import Data.Functor (void)
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import GHC.Generics (Generic)
import Test.QuickCheck (arbitrary, choose, vectorOf)
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.Random (mkQCGen)

type Hash = Bytes

type BlockBody = Bytes

data InputBlock = MkInputBlock
  { blockId :: Hash
  , blockTimestamp :: Integer -- in seconds/slots
  , blockData :: BlockBody
  }
  deriving (Show, Generic)
  deriving anyclass (A.ToJSON, A.FromJSON)

data EndorserBlock = MkEndorserBlock
  { endorserId :: Hash
  , endorsementTimestamp :: Integer
  , inputBlocks :: [Hash]
  , queueSize :: Int
  , droppedBlocks :: Int
  }
  deriving (Show, Generic)
  deriving anyclass (A.ToJSON, A.FromJSON)

data LeiosEvent
  = OutputEB EndorserBlock

instance A.ToJSON LeiosEvent where
  toJSON = \case
    OutputEB eb -> toJSON eb

data Params = Params
  { λ :: Integer
  -- ^ The length of the IB diffusion period, in rounds
  , capacity :: Integer
  -- ^ The maximum bandwidth of a node, in blocks
  , seed :: Integer
  -- ^ The initial seed value for random numbers generation
  , initialRound :: Integer
  -- ^ Starting round for simulation
  }

runSimulation :: (MonadAsync m, MonadDelay m, MonadSay m) => Tracer m LeiosEvent -> Params -> m ()
runSimulation tracer Params{λ, capacity} = do
  inputChannel <- newTQueueIO
  outputChannel <- newTQueueIO
  void $
    generateInput capacity λ 42 10 inputChannel
      `race` runNode λ 43 10 inputChannel outputChannel
      `race` observeOutput tracer outputChannel

observeOutput :: (MonadSTM m, MonadSay m) => Tracer m LeiosEvent -> TQueue m EndorserBlock -> m ()
observeOutput tracer output = forever go
 where
  go = do
    block <- atomically $ readTQueue output
    traceWith tracer (OutputEB block)

runNode :: (MonadSTM m, MonadDelay m) => Integer -> Int -> Integer -> TQueue m InputBlock -> TQueue m EndorserBlock -> m ()
runNode λ seed round input output =
  go seed round
 where
  go seed round = do
    let endorserId = genHash `generateWith` seed
    (blocks, queueSize, droppedBlocks) <- atomically $ do
      -- TODO: read at most capacity blocks
      allBlocks <- flushTQueue input
      let sortBlocks b (ontime, younger) =
            case (blockTimestamp b + λ) `compare` round of
              EQ -> (b : ontime, younger)
              GT -> (ontime, b : younger)
              LT -> (ontime, younger)
          (onTime, younger) =
            foldr sortBlocks ([], []) allBlocks
          dropped = length allBlocks - length onTime - length younger
      forM_ younger (writeTQueue input)
      pure (onTime, length younger, dropped)

    let endorserBlock =
          MkEndorserBlock
            { endorserId
            , endorsementTimestamp = fromIntegral round
            , inputBlocks = blockId <$> blocks
            , queueSize
            , droppedBlocks
            }

    atomically $ writeTQueue output endorserBlock
    let seed' = newSeed seed
    threadDelay 100000
    go seed' (succ round)

generateInput :: (MonadSTM m, MonadDelay m) => Integer -> Integer -> Int -> Integer -> TQueue m InputBlock -> m ()
generateInput capacity λ seed round channel =
  go seed round
 where
  go seed round = do
    let blocks = genBlocks capacity λ round `generateWith` seed
    atomically $ forM_ blocks $ writeTQueue channel
    threadDelay 100000
    let seed' = newSeed seed
    go seed' (succ round)

newSeed :: Int -> Int
newSeed = (* 2147483647)

genBlocks :: Integer -> Integer -> Integer -> Gen [InputBlock]
genBlocks capacity λ atRound = do
  let maxThroughput = fromInteger $ capacity * λ `div` (λ + 1)
  numBlocks <- choose (maxThroughput `div` 2, maxThroughput)
  vectorOf numBlocks $ genInputBlock atRound

genInputBlock :: Integer -> Gen InputBlock
genInputBlock atRound = do
  blockId <- genHash
  pure MkInputBlock{blockId, blockTimestamp = atRound, blockData = "00"}

genHash :: Gen Hash
genHash =
  Bytes . BS.pack <$> vectorOf 8 arbitrary

-- | Utility function for pure arbitrary values.
generateWith :: Gen a -> Int -> a
generateWith (MkGen runGen) seed =
  runGen (mkQCGen seed) 30
