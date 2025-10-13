---
sidebar_position: 3
---

# System Performance Under Load

## Concern

Community feedback expressed concerns about system degradation under high demand, referencing Figure 9 of the CIP as evidence that proposed Leios exhibits poor performance characteristics as load increases.

> "As you increase load you reach a maximum throughput and then the throughput will dropoff as you [continue to] increase load... it's a given that delays will increase."

<div style={{display: 'flex', justifyContent: 'center', margin: '20px 0'}}>
  <iframe 
    width="900" 
    height="506" 
    src="https://www.youtube.com/embed/XPwDkHsGYO8?start=630&end=720" 
    title="Community Discussion on Leios Performance Under Load" 
    frameBorder="0" 
    allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" 
    allowFullScreen
    style={{maxWidth: '100%', minHeight: '400px', aspectRatio: '16/9'}}
  />
</div>

## Analysis

The concern appears to stem from a misinterpretation of Figure 9 in the CIP specification. This figure represents a **limit analysis** used for parameter selection, not operational recommendations or expected system behavior.

### Purpose of Figure 9

Figure 9 from the [CIP specification](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#figure-9) demonstrates system behavior across a wide range of protocol parameters to identify optimal operating points.

<img 
  src="https://raw.githubusercontent.com/cardano-scaling/CIPs/leios/CIP-0164/images/reach-rb-tx.svg" 
  alt="Figure 9: Time for transaction to reach the ledger"
  style={{maxWidth: '100%', height: 'auto', display: 'block', margin: '20px auto'}}
/>

<div style={{textAlign: 'center'}}>
[*Figure 9: Time for transaction to reach the ledger*](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#figure-9)
</div>

The higher throughput scenarios showing increased latency represent **overcapacity conditions** that would not be used in practice. These data points serve to:

- Establish safe operational boundaries
- Guide protocol parameter selection
- Demonstrate system limits for research purposes

### Operational Parameter Selection

The proposed Leios protocol parameters are selected from the **efficient region** of the parameter space, specifically avoiding the degraded performance zones shown in Figure 9. The system is designed to operate well within capacity limits where performance remains stable.

### Transaction Lifecycle 

The apparent latency increase in Figure 9's higher throughput scenarios reflects a shift in transaction processing patterns rather than system degradation:

- **Lower throughput**: Mix of fast RB inclusion and slower EB inclusion
- **Higher throughput**: Predominantly EB inclusion (by design)
- **Overcapacity**: Transactions queue in mempool (same as current Praos behavior)

This represents normal queueing behavior during congestion, not a fundamental protocol flaw.

### Comparison with Current System

The current Praos system exhibits similar behavior under congestion:
- Mempool saturation causes increased transaction latency
- Throughput plateaus at maximum capacity
- Performance degrades when demand exceeds capacity

Proposed Leios maintains these same characteristics while providing significantly higher baseline throughput.

### Recent Simulation Improvements

Following community feedback, the research team conducted additional analysis to test the specific performance concerns raised. This investigation led to the discovery and resolution of a simulation bug that was artificially degrading performance metrics.

**Bug Discovery**: The Rust simulator was incorrectly including duplicate transactions in the ledger, which:
- Lowered effective throughput proportional to the redundancy
- Clogged the memory pool and slowed simulations
- Created misleading performance degradation patterns

**Resolution**: The bug was fixed in [sim-cli 1.3.1](https://github.com/input-output-hk/ouroboros-leios/releases/tag/sim-rs-1.3.1), and new simulations show that the protocol achieves its theoretical capacity more effectively than previously measured.

**Improved Results**: Updated simulations demonstrate that throughput properly plateaus at capacity limits rather than degrading, confirming that the protocol design meets its performance objectives under load.

## Conclusion

Figure 9 represents a comprehensive analysis of system limits used for parameter selection, not a prediction of operational performance. The proposed protocol parameters are specifically chosen to avoid the degraded performance regions, ensuring stable operation under normal and high-load conditions.

The recent discovery and correction of simulation bugs demonstrates the value of community feedback in improving both the protocol analysis and documentation. The corrected simulations show even better performance characteristics than originally reported.

---

**References**: [CIP Leios Specification - Figure 9](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#figure-9)
