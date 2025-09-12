# Topology for a Cardano mainnet analog for Leios simulations

The aim of the pseudo-mainnet topology is to have a Leios network that is generally representative of the Cardano mainnet:

- Realistic stake distribution
- Realistic number of stake pools
- Two relays for each block producer
- Block producers only connected to their relays
- 10,000 nodes total
- Realistic latencies, generally consistent with the [RIPE Atlas](https://atlas.ripe.net/) `ping` dataset
- Bandwidth consistent with the low end of what is generally available in cloud data centers
- Node connectivity generally consistent with measurements by the [Cardano Foundation](https://cardanofoundation.org/)
- Geographic distribution (countries and autonomous systems) consistent with measurements by the [Cardano Foundation](https://cardanofoundation.org/)


## Version 1: "pseudo-mainnet"

- Network: [topology-v1.yaml](topology-v1.yaml)
- Results of [topology checker](../../../topology-checker): [topology-v1.md](topology-v1.md)
- Jupyter notebook used for creating the network: [topology-v1.ipynb](topology-v1.ipynb)

> [!WARNING]
> 
> This is the first cut at a realistic mainnet-scale topology for Leios, but it likely contain imperfections, but it likely contain imperfections because several compromises were made during its construction, so as to smooth out inconsistencies in source data. It does pass the topology checks, however, and approximately matches the marginal distributions of key network metrics.


## Version 2: "mini-mainnet"

- Network: [topology-v2.yaml](topology-v2.yaml)
- Results of [topology checker](../../../topology-checker): [topology-v2.md](topology-v2.md)
- Jupyter notebook used for creating the network: [topology-v2.ipynb](topology-v2.ipynb)


## Version 3: "micro-mainnet"

- Network: [topology-v3.yaml](topology-v3.yaml)
- Results of [topology checker](../../../topology-checker): [topology-v3.md](topology-v3.md)
- Jupyter notebook used for creating the network: [topology-v3.ipynb](topology-v3.ipynb)


