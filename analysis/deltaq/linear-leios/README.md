# DeltaQ / Statistics library for Ourobors Praos and Leios

The library provides a [DeltaQ](https://github.com/DeltaQ-SD/deltaq/) model for Linear Leios.

## DeltaQ backend
The piecewise-polynomial backend in DeltaQ is [not built for modeling complex systems](https://github.com/DeltaQ-SD/deltaq/blob/main/doc/reports/artefact-A4.md#conclusion-and-next-steps). Due to this restriction, for running the model for Linear Leios we implemented a new, [experimental backend](https://github.com/yveshauser/deltaq/blob/experimental/lib/deltaq/src/DeltaQ/Sampled.hs) for DeltaQ that operates on discrete values representing a probability distribution.

## Running the code

Run the analysis generate diagrams as follows:

```
$ cabal run leios-deltaq-analysis stats
```
```
$ cabal run leios-deltaq-analysis plots
```
```
$ cabal run leios-deltaq-analysis estimates
```
