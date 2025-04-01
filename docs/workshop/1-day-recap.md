# Edinburgh Workshop Day 1 Recap

## Ledger Design Solution Space Matrix

┌─────────────────────┬──────────────────────────────────┬──────────────────────────────────┐
│                     │          Labeled UTxOs           │             Accounts             │
│                     │        (Explicit Shards)         │        (Implicit Shards)         │
├─────────────────────┼──────────────────────────────────┼──────────────────────────────────┤
│        Fees         │ • Explicit shard labeling        │ • Staking credential             │
│                     │ • Consumed on every tx           │   defines shard                  │
│                     │ • Bootstrap: requires            │ • No replay protection           │
│                     │   additional transaction         │ • No bootstrap transaction       │
│                     │ • Strong guarantees              │   needed                         │
│                     │                                  │ • Registration costs             │
├─────────────────────┼──────────────────────────────────┼──────────────────────────────────┤
│     Collateral      │ • Only consumed on               │ • Only consumed on               │
│                     │   conflicts                      │   conflicts                      │
│                     │ • Return address needed          │ • No replay protection           │
│                     │ • Helps prevent conflicts        │                                  │
├─────────────────────┼──────────────────────────────────┼──────────────────────────────────┤
│ All-Labeled Inputs  │ • Every input gets labeled       │                                  │
│    (Extension)      │ • Maximum conflict prevention    │                                  │
│                     │ • Higher bootstrapping cost      │               N/A                │
│                     │                                  │                                  │
└─────────────────────┴──────────────────────────────────┴──────────────────────────────────┘

### Labeled UTxOs - Fees
Explicit shard labeling of UTxOs with fees consumed on every transaction. Provides strong guarantees for conflict prevention. Requires one initial bootstrap transaction to transition from Praos to Leios, enabling immediate protocol participation.

### Labeled UTxOs - Collateral
Collateral consumed only when conflicts occur, requiring a return address. Offers weaker guarantees than the fees approach while maintaining system integrity through explicit shard labeling. Provides a more relaxed constraint on fee payment.

### Labeled UTxOs - All-Labeled Inputs Extension
The all-labeled inputs extension represents the most comprehensive approach, where every input gets labeled. This provides maximum conflict prevention but comes with higher bootstrapping costs. This approach offers the strongest guarantees but requires significant upfront work for migration.

### Accounts - Fees
The Accounts approach uses staking credentials to implicitly define shards, eliminating the need for explicit bootstrap transactions. However, it lacks replay protection and has registration costs. This approach is more natural for existing Cardano users but requires careful consideration of replay attacks.

### Accounts - Collateral
In the Accounts approach, collateral is only consumed on conflicts but lacks replay protection. This simpler mechanism avoids double spending but may be less robust against certain types of attacks. The integration with existing staking credentials makes it more user-friendly but potentially less secure.

### Accounts - All-Labeled Inputs Extension
This extension is not applicable to the Accounts approach.

## Hybrid Solution

```
┌─────────────────────────────────────────────────────────────┐
│                     Hybrid Ledger Design                    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│ 1. Default Transaction                                      │
│    ┌─────────────────────────────────────────────────────┐  │
│    │ • Implicit Shard (via Account)                      │  │
│    │ • Required UTxO Input                               │  │
│    │ • Optional Labeled Output                           │  │
│    └─────────────────────────────────────────────────────┘  │
│                                                             │
│ 2. Specialized Transaction                                  │
│    ┌─────────────────────────────────────────────────────┐  │
│    │ • Fully Labeled UTxOs                               │  │
│    │ • High-throughput Use Cases                         │  │
│    └─────────────────────────────────────────────────────┘  │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### How it works:

1. **Default Behavior**: 
   - Uses staking credential to implicitly define the shard
   - Requires at least one UTxO input for replay protection
   - Fees are covered by the reward account associated with the staking credential
   - UTxO is only consumed to prevent replay, not for fee payment

2. **Bootstrapping Process**:
   - New users can immediately use Leios without explicit migration
   - Transactions can only fail due to double spending (not fee insufficiency)
   - Always pays transaction fees from the reward account

3. **Migration Path**:
   - Users can optionally create transaction outputs with explicit shard IDs
   - High-throughput applications can migrate to fully labeled UTxOs
   - Gradual transition path rather than a hard cutover

4. **Edge Cases Addressed**:
   - **New Users**: Exchange withdrawals can work immediately without having to register reward accounts first
   - **Replay Protection**: Required UTxO input prevents transaction replay attacks
   - **Fee Payment**: Guaranteed through reward accounts, while maintaining strong conflict resolution

## Key Considerations

1. **Governance Interactions**:
   - The hybrid model can handle UTxO and reference inputs
   - Compatible with governance actions (votes and proposals)
   - Supports reward account withdrawals
   - Works with treasury assertions and parameter changes

2. **Pure Leios System**:
   - The hybrid approach provides a path to eventually create a pure Leios system
   - Can bootstrap with an initial distribution that includes both labeled UTxOs and account-based shards

3. **Critical Insight**:
   - A pure reward account approach is not viable due to:
     - Bootstrapping challenges for new users
     - Complexity of first-time transactions from exchanges
     - Handling empty reward accounts
     - New user onboarding limitations:
       - Exchange withdrawals require complex transactions
       - Need for receiving wallet signatures on exchange withdrawals
       - Impractical for first-time users entering through exchanges
     - Recovery challenges:
       - Users can become locked out if they accidentally empty their fee account
       - No mechanism to recover from empty reward accounts
       - Requires careful consideration of account balance management


> [!NOTE]
> 
> **Edge Case: New User Onboarding**
> 
> A significant challenge arises when new users enter Cardano through exchanges. Since they don't have a registered reward account, their first transaction would need to both register a staking credential and handle the exchange withdrawal. This creates a complex transaction that would require the receiving wallet to sign it, which is impractical for exchange withdrawals. This limitation makes pure account-based approaches problematic for new user onboarding.


## Conclusion

The hybrid approach to Leios ledger design offers the most pragmatic path forward, combining the security benefits of labeled UTxOs with the ease of adoption from account-based sharding. By requiring a UTxO input for replay protection while using reward accounts for fee payment, we can ensure both system security and a smooth transition from Praos to Leios.

