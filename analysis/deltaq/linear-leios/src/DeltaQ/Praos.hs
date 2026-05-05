-- | The module proposes a model for block diffusion of Ouroboros Praos.
--
-- Most of the code is from [Modelling Block Diffusion in Cardano using ∆Q](https://github.com/IntersectMBO/cardano-formal-specifications)
module DeltaQ.Praos (
  -- * Types
  BlockSize (..),

  -- * DeltaQ
  sendRBHeader,
  sendCertRBBody,
  sendTxRBBody,

  -- * Utils
  blockSizes,
  blendedDelay,
) where

import DeltaQ (DQ, Outcome (wait), ProbabilisticOutcome (choices))
import DeltaQ.Common (doSequentially)

data BlockSize = B1 | B64 | B256 | B512 | B1024 | B2048
  deriving (Show, Eq)

blockSizes :: [BlockSize]
blockSizes = [B1, B64, B256, B512, B1024, B2048]

short :: BlockSize -> DQ
short B1 = wait 0.012 -- HACK(SN): one RTT
short B64 = wait 0.024
short B256 = wait 0.047
short B512 = wait 0.066
short B1024 = wait 0.078
short B2048 = wait 0.085

medium :: BlockSize -> DQ
medium B1 = wait 0.069 -- HACK(SN): one RTT
medium B64 = wait 0.143
medium B256 = wait 0.271
medium B512 = wait 0.332
medium B1024 = wait 0.404
medium B2048 = wait 0.469

long :: BlockSize -> DQ
long B1 = wait 0.268 -- HACK(SN): one RTT
long B64 = wait 0.531
long B256 = wait 1.067
long B512 = wait 1.598
long B1024 = wait 1.598
long B2048 = wait 1.867

hop :: BlockSize -> DQ
hop b = choices [(1, short b), (1, medium b), (1, long b)]

hops :: Int -> BlockSize -> DQ
hops n b = doSequentially (replicate n (hop b))

-- | hopCount
--
-- Values are taken from [topology checker](https://github.com/input-output-hk/ouroboros-leios/tree/main/topology-checker)
-- tool in the ouroboros-leios project generated with the mainnet like network topology
hopCount :: [(Int, Rational)]
hopCount = [(1, 1909), (2, 3867), (3, 2826), (4, 1068), (5, 214), (6, 16)]

-- | lengthProbsNode10
--
-- The original Praos model
lengthProbsNode10 :: [(Int, Rational)]
lengthProbsNode10 = [(1, 0.40), (2, 3.91), (3, 31.06), (4, 61.85), (5, 2.78)]

-- | blendedDelay
blendedDelay :: BlockSize -> DQ
blendedDelay b = choices $ map (\(n, p) -> (p, hops n b)) lengthProbsNode10

-- NOTE(SN): A block header is ~1000B
sendRBHeader :: DQ
sendRBHeader = blendedDelay B1

-- NOTE(SN): A CertRB is ~500B
sendCertRBBody :: DQ
sendCertRBBody = blendedDelay B1

-- TODO(SN): A full praos block / TxRB can be up to 80kB
sendTxRBBody :: DQ
sendTxRBBody = blendedDelay B64
