# Leios cost estimates 

During the April 2025 status meeting, Input Output presented preliminary cost estimates for operating nodes under the proposed Leios protocol. The following section summarizes those estimates in a structured manner, compares expected operating costs under Leios with those of the current Ouroboros Praos protocol, and outlines indicative transaction-fee revenue assumptions.

## Why does it matter?

Under the current Ouroboros Praos protocol, the network produces one block approximately every 20 seconds, resulting in an average throughput of around 3.5 TPS for typical transaction sizes. Leios introduces additional block types, including input blocks (IBs), which decouple transaction dissemination from final ordering. This design aims to support substantially higher throughput, potentially reaching hundreds or thousands of TPS, depending on configuration and network conditions. If realized in practice, this increase in capacity would provide greater headroom for decentralized applications and broader ecosystem growth, while maintaining the underlying security model of Cardano’s consensus layer.

## Breaking down the costs

Operating a blockchain node incurs infrastructure costs, including compute resources, memory, storage, network data transfer (egress), and input/output operations per second (IOPS). The Leios team evaluated these cost components across several cloud providers. The analysis compares Leios with Ouroboros Praos at an equivalent throughput of 0.05 IB/s, corresponding to one input block every 20 seconds, and models projected costs at higher rates up to 30 IB/s.

- **At Praos-equivalent throughput (0.05 IB/s):**
  - On premium providers like AWS or Google Cloud, a Leios node costs ~$90–$114/month, slightly more than Praos due to voting overhead
  - On budget-friendly providers like Linode or Hetzner, costs range from $15–$65/month, making Leios accessible for node operators

- **At higher throughput (eg, 1 IB/s or 30 IB/s):**
  - Costs scale with throughput – at 1 IB/s (~70 TPS for average transactions), AWS costs ~$233/month, while Hetzner stays at ~$32/month
  - At 30 IB/s (~2,100 TPS), costs range from $450–$1,000/month on Linode/Hetzner to $4,000–$5,000/month on AWS/Google Cloud

These are early estimates, and we’re actively researching ways to optimize costs. The choice of cloud provider significantly impacts expenses, giving operators flexibility to match their budgets.

## Revenue potential from transaction fees

Leios’s higher throughput means more transactions, which boosts revenue from transaction fees. Cardano’s fee structure includes a fixed 0.155381 ada plus 0.000044056 ada per byte. For an average transaction (1,400 bytes), here’s the network’s potential revenue:

- **0.05 IB/s (3.5 TPS):** ~1.97M ada/month (~$887,000 at $0.45/ada)
- **1 IB/s (70 TPS):** ~39.4M ada/month (~$17.7M)
- **30 IB/s (2,100 TPS):** ~1.18B ada/month (~$531M)

Even modest throughput increases could cover infrastructure costs for Cardano’s ~10,000 nodes (including 3,000 stake pool operators and DApp nodes). For example, covering $800,000 in costs (at 0.05 IB/s) requires ~1.78M ada, achievable with just 3.5 TPS of average transactions.

## Looking ahead towards sustainability

As Cardano’s reserves decrease, transaction fees will play a bigger role in sustaining network rewards (~48M ada/month today). By 2030, with reserves potentially halved, Leios’s high TPS could generate enough fees to maintain rewards. At 30 IB/s, the network could support over 11,790 TPS for smaller transactions, ensuring long-term sustainability.

## What’s next?

These figures are preliminary, and the Leios team is working to make the protocol even more cost-efficient. Want to dive deeper? Check out the full calculations in this [GitHub repository](https://github.com/input-output-hk/ouroboros-leios/).
