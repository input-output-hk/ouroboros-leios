TODO: Sketch individual consensus components from [1], using [2] for miniprotocols details.

* Upstream peers: Uᵢfor i = 1..n
* Downsream peers: Dⱼ for j = 1..m

Shared state:
* forall i ∈ 1..n, Cᵢ:: Chain Header -- our view of upstream peer's chain.
* ChainState :: "Map BlockId Block" morally, but also taking care of last bit of chain selection?
  - CPref :: Chain Block -- our current preferred chain.
* forall i ∈ 1..n, RQᵢ:: [Header] -- which blocks should be fetched from the peer.

Threads:
* blockForge(ChainState)
  - only thread aware of slots
  - adds a new block to the current chain when time comes.

* for all i ∈ 1..n. chainSyncConsumer(Uᵢ, Cᵢ, ChainState.CPref)
  - our current chain is used to find initial intersection point with producer?

* blockFetchController([(Uᵢ, Cᵢ, RQᵢ)]ᵢ, ChainState)
   - From ChainState needs our current chain and which blocks we already have.

* for all i ∈ 1..n. blockFetchClient(Uᵢ, RQᵢ, ChainState)
   - newly added blocks added to ChainState should be considered for chain selection.
     - Duncan was saying we might be able to present blocks in-order so the chain selection logic is easier.

* for all j ∈ 1..m. chainSyncProducer(Dⱼ, ChainState)
* for all j ∈ 1..m. blockFetchServer(Dⱼ, ChainState)












### References


[1] Introduction to the design of the Data Diffusion and Networking for Cardano Shelley,
    https://iohk.io/en/research/library/papers/introduction-to-the-design-of-the-data-diffusion-and-networking-for-cardano-shelley/

[2] The Shelley Networking Protocol,
    https://ouroboros-network.cardano.intersectmbo.org/pdfs/network-spec/network-spec.pdf
