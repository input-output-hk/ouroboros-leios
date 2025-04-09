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

The simplified diagram below shows respective lower and upper bounds for selecting an RB as ledger state reference for IB validation - each showing the extreme ends of trading off latency for security. Realistically, both are not good choices and some RB such as tip-3 might be more suitable. Note, that even the tip-3 example would introduce on average a delay of 3×20s = 60s before a user could reference outputs from a previously submitted transaction.

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

##### 1. **EB Reference**

IBs directly reference certified EBs, which themselves reference an older RB.

![EB Reference Approach](eb-reference.svg)

Different to the [IB-to-RB referencing](#ib-to-rb-reference-approach), this approach has IBs reference an EB instead which itself references an RB.

We briefly discussed an alternative design choice, in which IBs reference an EB and an RB. However, that design would result in many ledger states that would need to be computed and was therefore dismissed as too expensive.

In this design, one gets a ledger state for each RB which gives a ledger state for each EB to be reused and IBs are validated with respect to that same state. On the contrary, due to EBs referencing an RB, there is still the same trade-off to be made as in the [IB-to-RB reference approach](#ib-to-rb-reference-approach) - having to chose more or less stable RBs for EBs resulting in higher latency or higher loss in EBs.


##### 2. **EB-Chain**

In this approach IBs reference an EB which itself may reference another EB, which creates this chain of EBs that anchors on some older RB reference. Thus, EBs may have an RB reference or another EB reference of an EB that has not made it into an RB yet (full Leios variant). RBs on the other hand can only exactly reference one certified EB. IBs reference one of these EBs.

As a downside of this approach, it doesn't allow for EBs to reference one or more EBs. Therefore, it still has the same trade-off from the previous [IB-to-EB-to-RB](#1-ib-to-eb-to-rb-reference) approach, since these chains of EBs are anchored to RBs, which comes with this disadvantageous property of high latency, older stable RBs vs low latency, less stable RBs.

![EB Chain Approach](eb-chain.svg)

##### 3. **EB-DAG**

The EB DAG approach represents a sophisticated approach that leverages a directed acyclic graph (DAG) structure of Endorsement Blocks (EBs) to achieve both low latency and strong security guarantees. In this design:

![EB Chain Approach](eb-dag.svg)

- EBs can reference one or more older EBs that haven't been referenced by other EBs yet
- Ranking Blocks (RBs) reference exactly one EB
- Input Blocks (IBs) reference one of these EBs

**Key Advantages:**

1. **Low Latency with Security**: By allowing EBs to reference other EBs directly, the system achieves low latency while maintaining security. This is because EBs don't need to wait for RBs to be produced, creating a more efficient validation pipeline.

2. **Strong Inclusion Guarantee**: With EBs referencing other EBs, there's a strong property that EBs almost always make it into the chain, assuming the EB rate is approximately 1.5x that of RB rate.

3. **Efficient State Management**: Despite allowing multiple EB references, the system maintains computational efficiency. When computing ledger states for EBs in a chain, nodes can reuse the ledger state from referenced EBs and only replay the IBs in the current EB.

4. **Complete History**: EBs form a chain back to genesis, with the first EB referencing an RB, and subsequent EBs referencing only other EBs. This creates a complete and verifiable history of the chain's state.

5. **Deterministic State Count**: The number of ledger states a node needs to maintain is exactly equal to the number of EBs, providing predictable resource requirements.

**Implementation Details:**

1. **EB Ordering**: The system handles multiple pipelines running in parallel, each producing one RB. With parameters set for 1.5 EBs per stage (with randomness via VRF functions potentially producing more), there may be multiple EBs to choose from for inclusion in an RB.

2. **State Reconstruction**: When computing ledger states, nodes can efficiently reconstruct the state by reusing states from referenced EBs and only replaying new IBs, preventing computational overhead.

**Limitations:**

1. **No Transactions in RBs**: A notable limitation of this scheme is that RBs cannot contain transactions themselves, as they serve primarily as ordering mechanisms for the EB DAG.

> [!Note]
> [Here](./eb-dag-detailed.svg) is a version of the EB-DAG including IBs.

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

### Next Steps

Further analysis of the EB reference approach, particularly around:
   - EB ordering mechanisms
   - State reconstruction efficiency (computational cost)
   - Security guarantees
