-- | Runtime carrier for the SUT's leadership schedule (winning slots).
--
--   The Agda spec postulates @leadershipSchedule : List ℕ@ and binds it (via a
--   @COMPILE GHC@ pragma) to 'leadershipScheduleSlots' below.  Because the
--   generated MAlonzo module cannot import @Main@ (that would be an import
--   cycle), the actual schedule is passed in out-of-band: @Main@ computes it
--   (querying a running node through the cardano-api) and installs it with
--   'setLeadershipSchedule' before invoking the verifier.  The Agda side then
--   reads it back through the postulate binding.
module LeadershipSchedule (
  leadershipScheduleSlots,
  setLeadershipSchedule,
) where

import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)

{-# NOINLINE scheduleRef #-}
scheduleRef :: IORef [Integer]
scheduleRef = unsafePerformIO (newIORef [])

-- | Install the leadership schedule.  Must be called before verification.
setLeadershipSchedule :: [Integer] -> IO ()
setLeadershipSchedule = writeIORef scheduleRef

-- | The installed schedule, read by the Agda postulate binding.  Empty until
--   'setLeadershipSchedule' is called (the verifier then falls back to
--   harvesting winning slots from the trace).
{-# NOINLINE leadershipScheduleSlots #-}
leadershipScheduleSlots :: [Integer]
leadershipScheduleSlots = unsafePerformIO (readIORef scheduleRef)
