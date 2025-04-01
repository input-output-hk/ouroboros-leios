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

