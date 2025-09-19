module trace-parser where

open import Parser
open import ShortLeiosVerifier renaming (verifyTrace to verifyShortLeiosTrace)
open import LinearLeiosVerifier renaming (verifyTrace to verifyLinearLeiosTrace)
