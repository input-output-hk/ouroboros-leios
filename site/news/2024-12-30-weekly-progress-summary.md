---
title: Weekly Summary – December 30, 2024
authors:
- will
tags: [progress, update, weekly]
---

## Rust simulation

- Abandoned Waxman graph generation favoring a more straightforward distance-weighted approach to better control graph connectivity.

## Haskell simulation

- Added support for bounded and unbounded parallelism to the Leios node
- Fixed relay protocol messages to ensure ordered delivery
- Next steps include loading protocol configuration from disk and investigating
  endorser block (EB) inclusion rates.

## Revised analysis of votes and certificates

- Continued research on cryptographic options for Leios votes and certificates
- BLS was identified as the most viable option.

## Jupyter support for DeltaQ

- Introduced new high-performance Haskell packages for DeltaQ with comprehensive
  test suites.
