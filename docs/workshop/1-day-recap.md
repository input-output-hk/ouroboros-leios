# Edinburgh Workshop Day 1 Recap

## Ledger Design Solution Space Matrix

|                     | Labeled UTxOs (Explicit Shards) | Accounts (Implicit Shards) |
|---------------------|--------------------------------|---------------------------|
| **Fees**            | • Explicit shard labeling<br>• Consumed on every tx<br>• Bootstrap: requires additional transaction<br>• Strong guarantees | • Staking credential defines shard<br>• No replay protection<br>• No bootstrap transaction needed<br>• Registration costs |
| **Collateral**      | • Only consumed on conflicts<br>• Return address needed<br>• Helps prevent conflicts | • Only consumed on conflicts<br>• No replay protection |
| **All-Labeled Inputs (Extension)** | • Every input gets labeled<br>• Maximum conflict prevention<br>• Higher bootstrapping cost | N/A |

### Labeled UTxOs - Fees
Explicit shard labeling of UTxOs with fees consumed on every transaction. Provides strong guarantees for conflict prevention. Requires one initial bootstrap transaction to transition from Praos to Leios, enabling immediate protocol participation.

### Labeled UTxOs - Collateral
Collateral consumed only when conflicts occur, requiring a return address. Offers weaker guarantees than the fees approach while maintaining system integrity through explicit shard labeling.

### Labeled UTxOs - All-Labeled Inputs Extension
The all-labeled inputs extension represents the most comprehensive approach, where every input gets labeled. This provides maximum conflict prevention but comes with higher bootstrapping costs. This approach offers the strongest guarantees but requires significant upfront work for migration.

### Accounts - Fees
The Accounts approach uses staking credentials to implicitly define shards, eliminating the need for explicit bootstrap transactions. However, it lacks replay protection and has registration costs. This approach is more natural for existing Cardano users but requires careful consideration of replay attacks.

### Accounts - Collateral
In the Accounts approach, collateral is only consumed on conflicts but lacks replay protection. This simpler mechanism avoids double spending but may be less robust against certain types of attacks. The integration with existing staking credentials makes it more user-friendly but potentially less secure.

### Accounts - All-Labeled Inputs Extension
This extension is not applicable to the Accounts approach.

## Key Design Considerations & Insights

### User Bootstrapping Flow
- Initial transaction requires a UTxO input for replay protection
- Uses implicit sharding via staking credential
- Can create labeled outputs in same transaction
- Provides seamless user experience without separate bootstrap transaction

### Network Transition Considerations
- Existing Praos UTxOs and reward accounts remain valid
- Need to consider both:
  1. Network transition (Praos → Leios)
  2. Individual user onboarding into Leios
- Gradual transition possible without hard cutover

### Critical Edge Cases

1. **New User Onboarding**
   - Exchange withdrawals are a critical flow
   - Pure account-based approach problematic:
     - Would require registering staking credential
     - Complex transaction needing receiving wallet signature
     - Impractical for exchange withdrawals
   
2. **Account Recovery**
   - Risk of users accidentally emptying fee accounts
   - No built-in recovery mechanism for empty reward accounts
   - Requires careful balance management consideration

3. **Fee Payment**
   - Must ensure reward accounts have sufficient funds
   - Need to consider initial distribution and maintenance
   - Balance between user experience and security

### System Properties

1. **Replay Protection**
   - UTxO input requirement prevents transaction replay
   - Critical for system security
   - Must be maintained regardless of sharding approach

2. **Conflict Resolution**
   - Explicit vs implicit sharding tradeoffs
   - Impact on throughput and user experience
   - Balance between complexity and guarantees

3. **Governance Compatibility**
   - Must work with existing governance mechanisms
   - Support for:
     - UTxO and reference inputs
     - Votes and proposals
     - Reward account withdrawals
     - Treasury assertions
     - Parameter changes
     - Hardfork events

### Conformance Testing Considerations

Two complementary approaches were discussed for ensuring implementation correctness:

1. **QuickCheck Dynamic Approach**
   - Executable formal specification in Agda
   - Specification converted to Haskell using standard Agda compiler
   - QuickCheck Dynamic test driver for generating test cases
   - Test adapters needed for both Haskell and Rust simulations
   - Challenges:
     - Complex generator development for meaningful test cases
     - Need for adapters to interface with simulations
     - Higher implementation effort but enables adversarial testing

2. **Trace Verification Approach**
   - Uses simulation log files as input
   - Verifies traces against relational specification
   - Lower implementation overhead
   - Requires standardized log format between implementations
   - Limitations:
     - Only tests behaviors that naturally occur in simulations
     - May miss edge cases or adversarial scenarios
     - Cannot directly test invalid behaviors

3. **Coverage Enhancement Strategy**
   - Track which parts of specification are exercised by traces
   - Use Haskell Program Coverage (HPC) on generated code
   - Identify untested branches and conditions
   - Benefits:
     - Clear visibility of test coverage gaps
     - Guide development of targeted test scenarios
     - Help prioritize adversarial test case development

4. **Implementation Requirements**
   - Standardized logging format across implementations
   - Support for negative events (e.g., "could not produce IB")
   - Clear separation between node and environment
   - Ability to track specification coverage
   - Support for both valid and invalid test cases

5. **Phased Testing Strategy**
   - Start with trace verification for basic correctness
   - Add coverage tracking to identify gaps
   - Develop targeted test cases for uncovered scenarios
   - Implement QuickCheck approach for adversarial testing?
   - Focus on high-priority edge cases identified in coverage analysis
