---
sidebar_position: 2
---

# Protocol overview

Leios addresses three interconnected concerns often found in blockchains:

- Transaction diffusion
- Transaction validation and availability
- Transaction ordering.

By decoupling transaction processing from consensus, Leios allows for more
efficient and continuous resource usage (eg, CPU and bandwidth). Instead of
experiencing short bursts of network load when blocks are fully created,
validated, and diffused, Leios introduces two core components to facilitate this
decoupling:

## Input blocks (IBs)

- Validators (stakeholders or miners) bundle transactions into lightweight IBs
  at high speed
- IBs are generated concurrently, not sequentially, maximizing available
  bandwidth.

## Endorser blocks (EBs)

- EBs aggregate batches of IBs and undergo a two-phase voting process to certify
  their validity and availability
- This is necessary because blocks are divided into two parts: headers and
  bodies
- An input block will not be referenced by an endorser block if its body is not
  available.

## Key properties

The following properties set Leios apart from traditional blockchain protocols:

- **High throughput**: Leios achieves near-optimal transaction processing
  capacity, utilizing almost all available bandwidth
- **Low latency**: Transactions are confirmed quickly, with minimal delays
- **Robust security**: Leios effectively mitigates threats like protocol bursts,
  message replays, and equivocations
- **Fairness**: Honest participants contribute to block production
  proportionally to their resources (stake or computing power)
- **Scalability**: The system scales smoothly with network capacity and
  available CPU resources needed to run verifiable random function (VRF)
  lotteries, process blocks and votes, and generate certificates. It maintains
  high performance even as participation fluctuates.
