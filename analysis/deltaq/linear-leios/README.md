# DeltaQ / Statistics library for Ourobors Praos and Leios

The library provides a [DeltaQ](https://github.com/DeltaQ-SD/deltaq/) model for Linear Leios.

### Parameter estimates

Running the parameter estimation is done as follows:

```
$ cabal run leios-deltaq-estimates
```

### Statistics

The statistics depend on the protocol parameters and other configurations. The following values are calculated:

|Statistic|Dependencies|Description|
|---|---|---|
|`pHeaderOnTime`|$L\_{hdr}$|Probability that an RB header arrives during $L\_{hdr}$|
|`pValidating`|$L\_{hdr}$, $L\_{vote}$|Probability that an EB can be validated on time|
|`pQuorum`|`pValidating`, committee size, number SPO|Probability of reaching a quorum|
|`pInterruptedByNewBlock`|$L\_{hdr}$, $L\_{vote}$, $L\_{diff}$|Probability of getting a new block too early|
|`pCertified`|`pInterruptedByNewBlock`, `pQuorum`|Probability that there is a certificate in the next RB|
|`eCertified`|$L\_{hdr}$, $L\_{vote}$, $L\_{diff}$|Expected time for next certified block|

Run the statistics as follows:

```
$ cabal run leios-deltaq-stats
```

Results are written to `output.csv`.

### Plots

The plot shows the CDF for the EB diffusion times. We see in the diagram that an EB with convincing probability arrived within 14 (= 3*1 + 4 + 7) slots.

![](docs/validateEB.svg)

Generate the plots as follows:

```
$ cabal run leios-deltaq-plots
```

### Outcome diagram

Generate the outcome diagram for EB validation as follows:

```
$ cabal run leios-deltaq-diagrams
```

The diagram is written to `docs/EB-diffusion.svg`.
