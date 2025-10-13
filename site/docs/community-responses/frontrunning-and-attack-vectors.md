---
sidebar_position: 4
---

# Frontrunning and Attack Vectors

## Concern

Community feedback raised concerns about potential attack vectors in the proposed Leios protocol, specifically regarding frontrunning opportunities and resource waste attacks through empty or minimal blocks.

> "Empty blocks have value in Praos (chain length) but empty EBs are negative value in Leios... [this creates] frontrunning concerns."

<div style={{display: 'flex', justifyContent: 'center', margin: '20px 0'}}>
  <iframe 
    width="900" 
    height="506" 
    src="https://www.youtube.com/embed/XPwDkHsGYO8?start=1285&end=1405" 
    title="Community Discussion on Leios Attack Vectors" 
    frameBorder="0" 
    allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" 
    allowFullScreen
    style={{maxWidth: '100%', minHeight: '400px', aspectRatio: '16/9'}}
  />
</div>

## Analysis

The concerns about frontrunning and resource waste attacks require examination within the broader context of blockchain security and the existing Praos system.

### Frontrunning Context

Frontrunning opportunities in proposed Leios are fundamentally similar to those in the current Praos system:

**Current Praos**: Block producers can selectively include transactions from the mempool, enabling frontrunning through transaction ordering or exclusion.

**Proposed Leios**: Similar selective inclusion capabilities exist, but with increased throughput providing more opportunities overall. This represents a **quantitative** rather than **qualitative** change in frontrunning potential.

### Empty Block Analysis

The concern about "empty EBs having negative value" requires clarification:

- **Empty EBs**: Have zero bytes in length and trigger no diffusion or voting when announced
- **Minimal EBs**: Could theoretically waste voting resources relative to transaction throughput
- **Mitigation**: Protocol can enforce minimum EB size requirements to address disproportionate voting costs

### Resource Waste Attack Vectors

The potential for adversarial resource waste exists but must be evaluated against:

1. **Attack Cost**: Producing EBs requires winning sortition, limiting attack frequency
2. **Waste Magnitude**: Voting verification represents minimal computational cost (~600ms total across all validators)
3. **Existing Vulnerabilities**: Current Praos system has similar attack surfaces through mempool manipulation

### Comparative Security Analysis

Proposed Leios does not introduce fundamentally new attack vectors but may amplify existing ones due to increased throughput. However:

- **Detection**: Malicious behavior patterns are observable and can trigger community response
- **Cost-Benefit**: Attack costs generally exceed potential benefits
- **Mitigation**: Protocol parameters can be adjusted to minimize attack effectiveness

## Conclusion

While proposed Leios may increase the scale of certain attack opportunities due to higher throughput, it does not introduce qualitatively new vulnerabilities. The protocol includes mechanisms to mitigate resource waste attacks, and the increased frontrunning potential is a natural consequence of improved scalability rather than a design flaw.

Comprehensive security analysis and potential parameter adjustments can further minimize these risks while preserving the protocol's scalability benefits.

---

**References**: [CIP Leios Specification](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#specification)
