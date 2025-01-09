---
title: Weekly Progress Summary - December 16, 2024
authors:
- William Wolff
email: wolff.william@iohk.io
tags: [progress, update]
---

## Rust Simulation

- Optimized virtual clock to be lock-free, removing contention from the previous
  implementation.

## Haskell Simulation

- Merged Leios visualizations on `main`.
- Improved P2P visualization with block type differentiation and latency
  charting.

## Analysis of Vote Size and ALBA Certificates

- Estimated minimum possible size for votes using ephemeral keys or KES.
- Benchmarked CPU time for ALBA certificates.
