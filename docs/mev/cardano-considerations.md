# Cardano/eUTxO Considerations

How Cardano's architecture affects MEV compared to account-based chains.

## Why eUTxO Limits Some MEV

Cardano's eUTxO model provides structural defenses against certain MEV attacks common on Ethereum.

### Transaction Determinism

**Property**: Cardano transactions fully specify their inputs and outputs at submission time. The transaction either succeeds with exactly the specified outcome or fails entirely.

**MEV Implications**:
- No "transaction introspection" attacks where outcome depends on state at execution
- Slippage protection is deterministic rather than probabilistic
- Failed transactions don't consume fees (phase-1 failures)

**Contrast with Ethereum**: On Ethereum, transaction outcomes depend on global state at execution time, enabling attacks where the attacker manipulates state between submission and execution.

### No Global State Reads

**Property**: Plutus scripts cannot read arbitrary on-chain state during execution. They can only validate based on the transaction's specified inputs, outputs, and datum.

**MEV Implications**:
- Oracle manipulation attacks constrained to specific oracle UTxOs
- No "just-in-time" liquidity attacks that read pool state
- Cross-protocol MEV limited to explicitly composed transactions

### UTxO Contention as Natural Serialization

**Property**: When multiple transactions attempt to consume the same UTxO, only one can succeed.

**MEV Implications**:
- Sandwich attacks requiring sequential execution on same state naturally prevented
- Competition for MEV opportunities is explicit via UTxO contention
- Block producers must choose between competing transactions rather than ordering them

---

## Cardano-Specific Mitigations

### Deterministic Fees

Cardano's fee model is deterministic based on transaction size and computational units, not market-driven like Ethereum's gas auctions.

**MEV Impact**: Reduces "gas war" dynamics where MEV extractors bid up fees. However, block producers can still prioritize based on:
- Absolute fee amount
- Fee-to-size ratio
- Off-chain arrangements

### Time-Locked Outputs

Many Cardano protocols use time-locked UTxOs that can only be consumed after a specified slot.

**MEV Impact**: Creates natural ordering constraints that limit some front-running strategies. Attackers cannot accelerate time-locked outputs.
