# Edinburgh Workshop Day 3 Recap

Agenda

[1. First Full Leios Simulation Analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w13/analysis.ipynb)

[2. Optimistic Ledger State References](#2-optimistic-ledger-state-references)

3. Community

## 2. Optimistic Ledger State References

The discussion focused on different approaches for handling optimistic ledger state references in the Leios protocol. The core problem is how to validate Input Blocks (IBs) against a ledger state that is not yet settled in a Ranking Block (RB). This is essential for enabling transaction chaining, where new transactions can build upon the outputs of previous transactions.

### Problem Statement

Validating an Input Block (IB) requires a reference to a ledger state that can be used to verify the validity of its transactions. The choice of this reference state involves a trade-off between security and latency. The most secure approach is to reference the RB from k blocks ago, where k is defined as the stability horizon and represents the length of the volatile chain suffix. This boundary provides perfect security as we can be confident that any older block referenced will be included in all possible futures of the chain. However, this approach introduces significant latency (potentially hours), making it impractical for many use cases that require quick transaction confirmation.

As we move to more recent blocks to reduce latency, we face increasing security challenges. Not every node in the network may have seen the same recent blocks due to network latency or temporary forks. For example, if an IB references the most recent RB, nodes that haven't received that RB yet cannot validate the IB. This creates a coordination problem where we need to ensure that the reference state is available to enough nodes to reach consensus on IB validity.

### Solution Space

Each of the following approaches describes a solution where an Input Block (IB) references a different block variant which provides a ledger reference for validation.

| Reference | Description | Security | Latency | Implementation<br />Complexity | Computational<br />Cost |
|-----------|-------------|----------|---------|--------------------------|-------------------|
| [RB](#rb-reference-approach) | IBs reference an older RB | Best | Worst | Best | Min |
| [EB](#eb-reference-approach) | IBs reference a certified Endorsement Block (EB) | Medium | Medium | Medium | Medium |
| [IB](#) | IBs reference other IBs | Worst | Best | Worst | Max |

> [!Note]
> The choice of referenceable ledger states cannot be arbitrary, not only due to security considerations but also due to practical system constraints. Maintaining too many potential reference states would lead to excessive memory usage and computational overhead as each node would need to track and validate numerous parallel ledger states. We have estimated the associated computation cost in the last column of each approach.

### Data Flow Diagrams

#### IB-to-RB Reference Approach

The simplified diagram below shows respective lower and upper bounds for selecting an RB as ledger state reference for IB validation - each showing the extreme ends of trading off latency for security. Realistically, both are not good choices and some RB such as tip-6 might be more suitable. Note, that even the tip-3 example would introduce on average a delay of 3×20s = 90s before a user could reference outputs from a previously submitted transaction.

![RB Reference Approach](rb-reference.svg)

> [!Note]
> The parameter k defines the stability horizon, which is the period during which the last k blocks of the chain remain mutable. After k blocks are added, all preceding blocks become immutable or in other words become part of the stable chain prefix.

Thus, we can define a new parameter to define stability for Leios which ranges between k on the upper bound and zero on the lower (representing the tip of the chain).

##### 1. Including EBs

![detailed](./rb-reference-detailed.svg)

This diagram shows the same ledger reference approach - pointing to RBs, but also includes EBs which have been hidden in the previous example for the stake of simplicity.

##### 2. Different IB-to-RB references

![complex](./rb-reference-realistic.svg)

The above diagram displays a more realistic picture of different IBs referencing different RBs as their ledger state reference for validation.

#### EB Reference Approach

The EB reference approach offers a middle ground between security and latency. Certified EBs (those that have received votes from a majority of stake) provide security guarantees with lower latency than the [RB-reference approach](#rb-reference-approach), as they indicate that enough nodes have seen and validated them. Several core variations of the EB reference approach were discussed:

1. **Direct EB Reference**: IBs directly reference certified EBs, which themselves reference an older RB.
![EB Reference Approach](eb-reference-01.svg)

2. **EB Chain Reference**: IBs reference an EB which itself may reference another EB, which creates this chain of EBs which at some point need to reference an RB. This approach allows for more recent state references while maintaining security through the chain of certified EBs, and handles scenarios where multiple certified EBs have been produced in parallel in the recent past.

TODO:
- EBs reference one or more older EBs (that have not been referenced by RBs)
- Each RB exactly ref one EB
- IBs reference one of these EBs
- No transactions in RBs!

3. **RB + EB Hybrid Reference**: IBs can reference either an RB or a certified EB, with the EB itself referencing an older RB. This provides flexibility while ensuring security. This was regarded as a bootstrap mechanism.

**Extensions and Implementation Details:**

- **Minimum Age Requirement**: A constraint where EBs must reference an RB that is at least a certain age (e.g., 5 minutes old) to ensure it's widely available in the network.

- **EB Ordering by Slot**: In the Leios protocol, multiple pipelines run in parallel, each ideally producing one RB. With parameters set for 1.5 EBs per stage (with randomness via VRF functions potentially producing more), there may be multiple EBs to choose from for inclusion in an RB. This approach orders EBs by slot number and VRF hash, with a predefined ordering function to resolve conflicts when multiple EBs exist for the same slot or from different pipelines.

- **Orphan Prevention**: A mechanism where RBs should not include EBs that reference orphaned EBs (those not included in previous RBs), helping to maintain a clear reference chain across pipelines.

- **EB State Reuse**: An optimization technique where, when computing ledger states for EBs in a chain, we reuse the ledger state from referenced EBs and only replay the IBs in the current EB, reducing computational overhead, especially important when dealing with multiple pipelines and stages.

#### IB Reference Approach

> [!Warning]
> We have not discussed this approach further and decided against progressing on it as it does not 
> meet the security requirements. It also comes with a high implementation complexity and
> computational overhead. The IB reference approach would require maintaining multiple speculative 
> ledger states, creating potential for state explosion and significantly increasing validation costs
> without providing adequate security guarantees.

### Key Considerations

1. **Security vs Latency Trade-off**: Each approach represents a different balance between security guarantees and latency reduction.

2. **State Management**: The certified EB reference approach requires careful management of EB ordering and state reconstruction, but provides a good balance of security and latency.

3. **Certification**: Certified EBs provide stability similar to RBs but with lower latency, making them a promising middle ground.

4. **Implementation Complexity**: The IB reference approach, while offering the lowest latency, introduces significant complexity in validation and security guarantees.

### Next Steps

1. Further analysis of the EB reference approach, particularly around:
   - EB ordering mechanisms
   - State reconstruction efficiency
   - Security guarantees

2. Simulation studies to quantify:
   - Latency improvements
   - State management overhead
   - Security properties

3. Consider hybrid approaches that combine elements from different strategies based on specific use cases.
