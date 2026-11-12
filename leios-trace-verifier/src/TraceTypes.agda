module TraceTypes where

open import Leios.Prelude using (Type; String; ℕ)
open import Protocol.BaseTypes public using () renaming (Slot to SlotNumber)

-- Identifiers from the log, not block payloads or spec-level hashes.
RBId EBId VTBundleId : Type
RBId       = String
EBId       = String
VTBundleId = String

-- Byte counts after converting the parser's Word64 Bytes to naturals.
ByteCount : Type
ByteCount = ℕ
