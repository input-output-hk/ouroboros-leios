# Edinburgh Workshop Day 3 Recap

Agenda

[1. First Full Leios Simulation Analysis](https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/sims/2025w13/analysis.ipynb)

2. Optimistic Ledger State References

3. Community

> [!Note]
> Check again later this week.

## 2. Optimistic Ledger State References

The discussion focused on different approaches for handling optimistic ledger state references in the Leios protocol. The core problem is how to validate Input Blocks (IBs) against a ledger state that is not yet settled in a Ranking Block (RB). This is essential for enabling transaction chaining, where new transactions can build upon the outputs of previous transactions that haven't yet been settled in a stable chain state, striking a careful balance between security and latency.

### Problem Statement

Validating an Input Block (IB) requires a reference to a ledger state that can be used to verify the validity of its transactions. The choice of this reference state involves a fundamental trade-off between security and latency. The most secure approach is to reference the RB from k blocks ago (the stability horizon in Praos), where k represents the length of the volatile suffix. This provides perfect security as we can be confident that such blocks will be included in all possible futures of the chain. However, this approach introduces significant latency (potentially hours), making it impractical for many use cases that require quick transaction confirmation.

As we move to more recent blocks to reduce latency, we face increasing security challenges. Not every node in the network may have seen the same recent blocks due to network latency or temporary forks. For example, if an IB references the most recent RB, nodes that haven't received that RB yet cannot validate the IB. This creates a coordination problem where we need to ensure that the reference state is available to enough nodes to reach consensus on IB validity.

### Validation Requirements

For an IB to be valid, it must be validated against a ledger state that:
1. Is available to a majority of nodes in the network
2. Has sufficient security guarantees (e.g., certified or stable)
3. Contains all necessary UTXOs and account states for transaction validation

The validation process requires:
- A deterministic way to reconstruct the ledger state
- Agreement among nodes about which state to use for validation
- Ability to handle cases where different nodes might have different views of the chain

This is particularly challenging because:
- Nodes may be at different points in the chain due to network conditions
- Short forks can create temporary inconsistencies
- The need for low latency conflicts with the need for stable reference points
- The stability horizon (k blocks) provides perfect security but introduces impractical latency

The trade-off between security and latency is fundamental:
- Using the stability horizon (k blocks back) provides perfect security but high latency
- Using more recent blocks reduces latency but requires additional mechanisms to ensure security
- Certified Endorsement Blocks (EBs) offer a middle ground, providing security guarantees with lower latency than the stability horizon

### Approaches

| Approach | Description | Pros | Cons |
|----------|-------------|------|------|
| RB Reference | IBs reference an older RB | - Simple to understand<br>- High security guarantees | - High latency<br>- Impractical for recent UTXOs |
| EB Reference | IBs reference a certified Endorsement Block (EB) | - Lower latency than RB reference<br>- Certified EBs provide stability | - Need to handle EB ordering<br>- More complex state management |
| IB Reference | IBs reference other IBs | - Lowest possible latency<br>- Most flexible | - Highest complexity<br>- Security challenges<br>- Harder to validate |

### Data Flow Diagrams

```d2
title: {
  label: "RB Reference Approach"
  near: top-center
  style.font-size: 24
  style.bold: true
  style.fill: "#ffffff"
  style.stroke: "#ffffff"
}

# Styles
classes: {
  rb: {
    style: {
      stroke: "#2a2a2a"
      fill: "#ffd700"  # Gold color for RBs
      font-color: "#2a2a2a"
      font-size: 16
      border-radius: 10
      shadow: true
    }
  }
  ib: {
    style: {
      stroke: "#2a2a2a"
      fill: "#90EE90"  # Light green for IBs
      font-color: "#2a2a2a"
      font-size: 16
      border-radius: 10
      shadow: true
    }
  }
  reference: {
    style: {
      stroke: "#1a73e8"
      fill: "#e8f0fe"
      font-color: "#1a73e8"
      border-radius: 15
      bold: true
    }
  }
}

# Blocks
RB1: {
  class: rb
  label: "RB1\n(Stable)"
}

RB2: {
  class: rb
  label: "RB2\n(Stable)"
}

IB1: {
  class: ib
  label: "IB1"
}

IB2: {
  class: ib
  label: "IB2"
}

# References
IB1 -> RB1: "References"
IB2 -> RB1: "References"

# Note
note: {
  class: reference
  label: "High Latency\nBut Simple"
}

# Layout
direction: right
```

```d2
title: {
  label: "EB Reference Approach"
  near: top-center
  style.font-size: 24
  style.bold: true
  style.fill: "#ffffff"
  style.stroke: "#ffffff"
}

# Styles
classes: {
  rb: {
    style: {
      stroke: "#2a2a2a"
      fill: "#ffd700"  # Gold color for RBs
      font-color: "#2a2a2a"
      font-size: 16
      border-radius: 10
      shadow: true
    }
  }
  eb: {
    style: {
      stroke: "#2a2a2a"
      fill: "#87CEEB"  # Sky blue for EBs
      font-color: "#2a2a2a"
      font-size: 16
      border-radius: 10
      shadow: true
    }
  }
  ib: {
    style: {
      stroke: "#2a2a2a"
      fill: "#90EE90"  # Light green for IBs
      font-color: "#2a2a2a"
      font-size: 16
      border-radius: 10
      shadow: true
    }
  }
  reference: {
    style: {
      stroke: "#1a73e8"
      fill: "#e8f0fe"
      font-color: "#1a73e8"
      border-radius: 15
      bold: true
    }
  }
}

# Blocks
RB1: {
  class: rb
  label: "RB1\n(Stable)"
}

EB1: {
  class: eb
  label: "EB1\n(Certified)"
}

EB2: {
  class: eb
  label: "EB2\n(Certified)"
}

IB1: {
  class: ib
  label: "IB1"
}

IB2: {
  class: ib
  label: "IB2"
}

# References
EB1 -> RB1: "References"
EB2 -> EB1: "References"
IB1 -> EB1: "References"
IB2 -> EB2: "References"

# Note
note: {
  class: reference
  label: "Balanced Latency\nAnd Security"
}

# Layout
direction: right
```

```d2
title: {
  label: "IB Reference Approach"
  near: top-center
  style.font-size: 24
  style.bold: true
  style.fill: "#ffffff"
  style.stroke: "#ffffff"
}

# Styles
classes: {
  rb: {
    style: {
      stroke: "#2a2a2a"
      fill: "#ffd700"  # Gold color for RBs
      font-color: "#2a2a2a"
      font-size: 16
      border-radius: 10
      shadow: true
    }
  }
  ib: {
    style: {
      stroke: "#2a2a2a"
      fill: "#90EE90"  # Light green for IBs
      font-color: "#2a2a2a"
      font-size: 16
      border-radius: 10
      shadow: true
    }
  }
  reference: {
    style: {
      stroke: "#1a73e8"
      fill: "#e8f0fe"
      font-color: "#1a73e8"
      border-radius: 15
      bold: true
    }
  }
}

# Blocks
RB1: {
  class: rb
  label: "RB1\n(Stable)"
}

IB1: {
  class: ib
  label: "IB1"
}

IB2: {
  class: ib
  label: "IB2"
}

IB3: {
  class: ib
  label: "IB3"
}

# References
IB1 -> RB1: "References"
IB2 -> IB1: "References"
IB3 -> IB2: "References"

# Note
note: {
  class: reference
  label: "Lowest Latency\nBut Insecure"
}

# Layout
direction: right
```

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