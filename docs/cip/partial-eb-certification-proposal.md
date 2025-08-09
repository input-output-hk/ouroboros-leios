# Partial Endorsement Block Certification via Merkle Trees

## Abstract

This proposal introduces a merkle tree-based approach to Endorsement Block (EB) certification in Leios, allowing Ranking Block (RB) producers to make progress with partially available transaction sets rather than requiring complete EB availability. This addresses the critical edge case where network conditions prevent full EB propagation within the required time bounds.

## Motivation

The current Linear Leios design faces a challenging edge case: when an RB producer receives an EB certificate but lacks the certified EB's contents, they cannot build the required ledger state. This creates a dilemma:

1. **Wait for the EB**: Violates the Δ_RB timing assumption, potentially compromising Praos security
2. **Build on different chain**: Leads to short forks and reduced chain growth
3. **Include invalid transactions**: Compromises the consensus guarantees

These solutions either weaken security assumptions or degrade user experience. We need a mechanism that allows forward progress while maintaining cryptographic soundness.

## Key Idea

Transform EBs from monolithic transaction lists into merkle trees, where:
- EB producers announce a merkle root of their transaction set
- Voters can vote on partial views (merkle paths) they've observed
- RB producers can include transaction subsets with merkle proofs
- Certificates attest to the merkle root, not complete contents

This enables **progressive consensus**: nodes agree on increasingly specific subsets as data propagates.

## Design Details

### 1. EB Structure

Replace the current EB structure:
```
Current: EB = [tx_id_1, tx_id_2, ..., tx_id_n]
Proposed: EB = MerkleRoot(OrderedTxTree)
```

Using an order-preserving structure like:
- **Indexed Merkle Tree**: Each leaf = `hash(index || tx_id)`
- **Merkle Mountain Range**: Natural append-order preservation
- **Vector Commitment**: Proves both membership and position

### 2. Hierarchical Voting

Voters cast votes on the deepest merkle path they can verify:

```
Vote = {
  eb_id: Hash,
  merkle_path: Path,
  path_depth: Integer,
  stake: Amount
}
```

Example voting tree:
```
Root (90% stake voted)
├── PathA (75% stake)
│   ├── PathA1 (60% stake) 
│   └── PathA2 (45% stake)
└── PathB (70% stake)
    └── PathB1 (65% stake)
```

### 3. Certificate Creation

An EB certificate includes:
```
Certificate = {
  merkle_root: Hash,
  total_tx_count: Integer,
  min_inclusion_threshold: Percentage,
  votes: [Vote]
}
```

### 4. RB Production Algorithm

When producing an RB with an EB certificate:

```python
def select_transactions(certificate, local_mempool):
    # Start from root
    current_path = certificate.merkle_root
    selected_txs = []
    
    # Traverse tree following highest-voted paths
    while can_go_deeper(current_path):
        children = get_children_paths(current_path)
        # Filter by: (1) sufficient votes, (2) local availability
        valid_children = filter(
            lambda p: has_quorum(p) and available_locally(p),
            children
        )
        if not valid_children:
            break
        current_path = max_votes(valid_children)
        selected_txs.extend(get_txs_at_path(current_path))
    
    return selected_txs, generate_merkle_proof(selected_txs)
```

### 5. Reward Mechanism

Proportional rewards based on inclusion:
```
reward = base_reward × (included_tx_count / total_tx_count)
```

This incentivizes maximum inclusion while allowing degraded operation.

## Security Considerations

### Advantages

1. **Graceful Degradation**: Network congestion causes reduced throughput, not complete stalls
2. **Maintained Consensus**: All nodes still agree on the certified merkle root
3. **Verifiable Partial Sets**: Merkle proofs ensure included transactions are legitimate
4. **Economic Alignment**: Rewards incentivize maximum feasible inclusion

### Potential Concerns

1. **Vote Dilution**: Stake might be spread across multiple paths rather than concentrated
2. **Complexity**: Increased computational and storage requirements for vote tracking
3. **Weaker Attestation**: Votes attest "I've seen at least X" rather than "I've seen exactly Y"

### Mitigations

- **Minimum Thresholds**: Require voters see >X% of transactions before voting
- **Depth Limits**: Bound merkle tree depth to limit complexity
- **Time Windows**: Longer L_vote periods to allow fuller propagation

## Comparison with Existing Proposals

| Approach | Pros | Cons |
|----------|------|------|
| **ThereIsNoProblem** | Simple, secure | Requires very fast EB propagation |
| **Shavasana** | Guaranteed time for propagation | Reduces throughput with empty RBs |
| **NonRecursiveRbValidity** | Always make progress | Invalid txs on chain, complex corrections |
| **Partial Certification** | Adaptive to network conditions | Increased protocol complexity |

## Implementation Considerations

1. **Merkle Structure Choice**: Need benchmarks for different order-preserving structures
2. **Vote Aggregation**: Efficient algorithms for tracking votes across tree paths  
3. **Network Protocol**: Extensions to gossip votes on partial paths
4. **Mempool Coordination**: Ensuring transaction availability alignment

## Open Questions

1. What minimum inclusion threshold provides adequate security?
2. How deep should merkle trees be for optimal performance/security trade-off?
3. Can vote aggregation be made efficient enough for mainnet scale?
4. How does this interact with adversarial EB producers who might create unbalanced trees?

## Conclusion

Merkle tree-based partial EB certification offers a promising middle ground between the rigid "all-or-nothing" current design and proposals that compromise on consensus guarantees. By enabling progressive consensus on transaction subsets, we can maintain forward progress during adverse network conditions while preserving cryptographic soundness and economic incentives.

This approach warrants further investigation through formal security analysis and simulation to validate its practical feasibility.