module Leios.Foreign.Util where

open import Leios.Prelude

postulate
  error : {A : Set} → String → A
{-# FOREIGN GHC import Data.Text #-}
{-# COMPILE GHC error = \ _ s -> error (unpack s) #-}
