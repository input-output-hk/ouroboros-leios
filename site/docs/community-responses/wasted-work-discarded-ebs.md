---
sidebar_position: 2
---

# Efficiency of Discarded Endorser Blocks

## Concern

A community member raised concerns about resource efficiency in the proposed Leios protocol:

> "All the work you've done, all the transmission you've done, all the voting you've done will be discarded [when EBs are discarded probabilistically]."

<div style={{display: 'flex', justifyContent: 'center', margin: '20px 0'}}>
  <iframe 
    width="900" 
    height="506" 
    src="https://www.youtube.com/embed/XPwDkHsGYO8?start=1018&end=1078" 
    title="Community Discussion on Leios Protocol Efficiency" 
    frameBorder="0" 
    allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" 
    allowFullScreen
    style={{maxWidth: '100%', minHeight: '400px', aspectRatio: '16/9'}}
  />
</div>

## Analysis

The proposed Leios protocol incorporates several design features that preserve computational work when Endorser Blocks (EBs) are discarded, making the characterization above inaccurate for honest network conditions.

### Transaction Processing Efficiency

A Leios node relies on caching mechanisms where nodes maintain local stores of previously processed transactions. When constructing new EBs, nodes prioritize transactions from discarded EBs. Since transactions are transmitted by reference rather than full content, subsequent EBs require minimal additional network overhead for previously seen transactions.

**Validation Work Reuse**: Crucially, the computational work spent validating transactions in a discarded EB is preserved. The protocol design includes multiple validation levels - when transactions are reused in subsequent EBs or RBs, nodes can apply cheaper revalidation methods rather than repeating expensive operations like script evaluation and signature verification.

### Voting Resource

The primary computational cost when EBs are discarded is indeed voting verification. However, this represents minimal resource consumption:

- **Vote size**: Under 200 bytes per vote
- **Verification time**: 1.4ms (unoptimized worst case) for ~100 non-persistent voters, 670μs for ~500 persistent voters
- **Total wasted time**: Approximately 600ms per discarded EB across all validators
- **Infrastructure context**: Stake Pool Operators provision significantly above average utilization to handle Praos' inherent demand spikes

This voting overhead was not identified as a concern by SPOs during consultation, as it utilizes the cheapest computational resources (network bandwidth and compute) that would otherwise remain idle.

### Resource Utilization

The voting overhead utilizes network bandwidth and computational resources that would otherwise remain idle in the current Praos system. This represents efficient use of already-provisioned infrastructure rather than additional operational burden.

## Conclusion

The protocol design specifically addresses efficiency concerns through transaction caching, reference-based transmission, and minimal voting overhead. The majority of computational and network transmission work is preserved even when EBs are discarded, contradicting the assertion that "all work is wasted."

---

**References**: [CIP Leios Specification](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#specification)
