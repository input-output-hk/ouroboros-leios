# Understanding Leios - A Look at Cost Estimates for Cardano’s Next Step

At IOG, we’re thrilled about the Leios project, a major leap toward enhancing Cardano’s scalability and efficiency. During last month’s status meeting, we shared early cost estimates for running Leios nodes. Here’s a straightforward breakdown of those figures, showing what it might cost to operate Leios compared to the current Praos protocol and the potential revenue from transaction fees.

## What is Leios, and Why Does It Matter?

Leios is designed to supercharge Cardano’s transaction throughput, enabling the network to process far more transactions per second (TPS) efficiently. While the current Praos protocol produces one block every 20 seconds (~3.5 TPS for average-sized transactions), Leios introduces Input Blocks (IBs) that can scale up significantly—potentially supporting thousands of TPS. This is a game-changer for developers building decentralized applications (dApps) and for Cardano’s ecosystem growth.

## Breaking Down the Costs

Running a blockchain node involves costs like computing power, memory, storage, network data transfer (egress), and input/output operations (IOPS). The Leios team analyzed these across various cloud providers, comparing Leios to Praos at equivalent throughput (0.05 IB/s, or one Input Block every 20 seconds) and at higher rates up to 30 IB/s.

- **At Praos-equivalent throughput (0.05 IB/s):**
  - On premium providers like AWS or Google Cloud, a Leios node costs ~$90–$114/month, slightly more than Praos due to voting overhead.
  - On budget-friendly providers like Linode or Hetzner, costs range from $15–$65/month, making Leios accessible for node operators.

- **At higher throughput (e.g., 1 IB/s or 30 IB/s):**
  - Costs scale with throughput. At 1 IB/s (~70 TPS for average transactions), AWS costs ~$233/month, while Hetzner stays at ~$32/month.
  - At 30 IB/s (~2,100 TPS), costs range from $450–$1,000/month on Linode/Hetzner to $4,000–$5,000/month on AWS/Google Cloud.

These are early estimates, and we’re actively researching ways to optimize costs. The choice of cloud provider significantly impacts expenses, giving operators flexibility to match their budgets.

## Revenue Potential From Transaction Fees

Leios’s higher throughput means more transactions, which boosts revenue from transaction fees. Cardano’s fee structure includes a fixed 0.155381 ADA plus 0.000044056 ADA per byte. For an average transaction (1,400 bytes), here’s the network’s potential revenue:

- **0.05 IB/s (3.5 TPS):** ~1.97M ADA/month (~$887,000 at $0.45/ADA).
- **1 IB/s (70 TPS):** ~39.4M ADA/month (~$17.7M).
- **30 IB/s (2,100 TPS):** ~1.18B ADA/month (~$531M).

Even modest throughput increases could cover infrastructure costs for Cardano’s ~10,000 nodes (including 3,000 stake pool operators and dApp nodes). For example, covering $800,000 in costs (at 0.05 IB/s) requires ~1.78M ADA, achievable with just 3.5 TPS of average transactions.

## Looking Ahead Towards Sustainability

As Cardano’s reserves decrease, transaction fees will play a bigger role in sustaining network rewards (~48M ADA/month today). By 2030, with reserves potentially halved, Leios’s high TPS could generate enough fees to maintain rewards. At 30 IB/s, the network could support over 11,790 TPS for smaller transactions, ensuring long-term sustainability.

## What’s Next?

These figures are preliminary, and the Leios team is working to make the protocol even more cost-efficient. Want to dive deeper? Check out the full calculations on our [GitHub repository](https://github.com/input-output-hk/ouroboros-leios/)!
