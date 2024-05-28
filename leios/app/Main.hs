{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Bytes (Bytes (..))
import Control.Concurrent.Class.MonadSTM (
  MonadSTM,
  TQueue,
  atomically,
  flushTQueue,
  newTQueueIO,
  readTQueue,
  writeTQueue,
 )
import Control.Monad (forM_)
import Control.Monad.Class.MonadAsync (race)
import Control.Monad.Class.MonadSay (MonadSay, say)
import Control.Monad.Class.MonadTimer (MonadDelay, threadDelay)
import qualified Data.Aeson as A
import qualified Data.ByteString as BS
import Data.Functor (void)
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import GHC.Generics (Generic)
import Test.QuickCheck (arbitrary, choose, listOf, vectorOf)
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

main :: IO ()
main = do
  let λ = 12
  inputChannel <- newTQueueIO
  outputChannel <- newTQueueIO
  void $
    generateInput λ 42 10 inputChannel
      `race` runNode λ 43 10 inputChannel outputChannel
      `race` observeOutput outputChannel

observeOutput :: (MonadSTM m, MonadSay m) => TQueue m EndorserBlock -> m ()
observeOutput output = do
  block <- atomically $ readTQueue output
  say $ LT.unpack $ LT.decodeUtf8 $ A.encode block
  observeOutput output

runNode :: (MonadSTM m, MonadDelay m) => Integer -> Int -> Integer -> TQueue m InputBlock -> TQueue m EndorserBlock -> m ()
runNode λ seed slot input output = do
  let endorserId = genHash `generateWith` seed
  (blocks, queueSize, droppedBlocks) <- atomically $ do
    allBlocks <- flushTQueue input
    let sortBlocks b (ontime, younger) =
          case (blockTimestamp b + λ) `compare` slot of
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
          , endorsementTimestamp = fromIntegral slot
          , inputBlocks = blockId <$> blocks
          , queueSize
          , droppedBlocks
          }

  atomically $ writeTQueue output endorserBlock
  let seed' = newSeed seed
  threadDelay 100000
  runNode λ seed' (succ slot) input output

generateInput :: (MonadSTM m, MonadDelay m) => Integer -> Int -> Integer -> TQueue m InputBlock -> m ()
generateInput λ seed slot channel = do
  let blocks = genBlocks λ slot `generateWith` seed
  atomically $ forM_ blocks $ writeTQueue channel
  threadDelay 100000
  let seed' = newSeed seed
  generateInput λ seed' (succ slot) channel

newSeed :: Int -> Int
newSeed = (* 2147483647)

genBlocks :: Integer -> Integer -> Gen [InputBlock]
genBlocks λ atSlot =
  listOf $ genInputBlock λ atSlot

genInputBlock :: Integer -> Integer -> Gen InputBlock
genInputBlock λ atSlot = do
  blockId <- genHash
  blockTimestamp <- choose (max 0 (atSlot - 2 * λ), atSlot - 1)
  pure MkInputBlock{blockId, blockTimestamp, blockData = "00"}

genHash :: Gen Hash
genHash =
  Bytes . BS.pack <$> vectorOf 8 arbitrary

-- | Utility function for pure arbitrary values.
generateWith :: Gen a -> Int -> a
generateWith (MkGen runGen) seed =
  runGen (mkQCGen seed) 30
