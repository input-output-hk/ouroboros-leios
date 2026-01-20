-- | The module proposes a model for block diffusion of Ouroboros Praos. See also
-- [Modelling Block Diffusion in Cardano using ∆Q](https://github.com/IntersectMBO/cardano-formal-specifications)
--
-- TODO:
--
-- * This will be replaced by a new model based on a queing model for the mem-pool, similar
-- to what is proposed the VECTOR paper.
module DeltaQ.Praos (
  -- * Types
  BlockSize (..),

  -- * DeltaQ
  emitRBHeader,
  fetchingRBBody,

  -- * Utils
  blockSizes,
  blendedDelay,
) where

import DeltaQ (DQ, Outcome (wait, (.>>.)), ProbabilisticOutcome (choices))

data BlockSize = B64 | B256 | B512 | B1024 | B2048
  deriving (Show, Eq)

blockSizes :: [BlockSize]
blockSizes = [B64, B256, B512, B1024, B2048]

short :: BlockSize -> DQ
short B64 = wait 0.024
short B256 = wait 0.047
short B512 = wait 0.066
short B1024 = wait 0.078
short B2048 = wait 0.085

medium :: BlockSize -> DQ
medium B64 = wait 0.143
medium B256 = wait 0.271
medium B512 = wait 0.332
medium B1024 = wait 0.404
medium B2048 = wait 0.469

long :: BlockSize -> DQ
long B64 = wait 0.531
long B256 = wait 1.067
long B512 = wait 1.598
long B1024 = wait 1.598
long B2048 = wait 1.867

hop :: BlockSize -> DQ
hop b = choices [(1, short b), (1, medium b), (1, long b)]

hops :: Int -> BlockSize -> DQ
hops n b = doSequentially (replicate n (hop b))
 where
  doSequentially :: [DQ] -> DQ
  doSequentially = foldr (.>>.) (wait 0)

blendedDelay :: BlockSize -> DQ
blendedDelay b = choices $ map (\(n, p) -> (p, hops n b)) hopCount
 where
  -- values are taken from topology checker tool
  hopCount = [(1, 1909), (2, 3867), (3, 2826), (4, 1068), (5, 214), (6, 16)]

emitRBHeader :: DQ
emitRBHeader = blendedDelay B64

fetchingRBBody :: DQ
fetchingRBBody = blendedDelay B1024
