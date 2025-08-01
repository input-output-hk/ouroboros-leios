// This file contains TypeScript types for the configuration file formats.

/** A configuration for a Leios simulation. */
export interface Config {
  // Simulation Configuration
  "relay-strategy": RelayStrategy;
  /** Only supported by Haskell simulation. */
  "tcp-congestion-control": boolean;
  /** Only supported by Haskell simulation. */
  "multiplex-mini-protocols": boolean;
  /** Only supported by Rust simulation. */
  "simulate-transactions": boolean;
  /**
   * When `true`, any delays and message sizes are calculated as if
   * each block contained as much data as the expected average, rounded up.
   * In particular, for the sake of the above, we consider that:
   *   - Each RB includes a certificate.
   *   - Certificates contain votes from `vote-threshold` nodes.
   *   - Vote bundles vote for `ceil eb-generation-probability` EBs.
   *   - EBs reference `ceil (ib-generation-probability * leios-stage-length-slots)` IBs.
   * Only supported by Haskell simulation. */
  "treat-blocks-as-full": boolean;
  /** Only supported by Haskell simulation. */
  "cleanup-policies": CleanupPolicies;
  /**
   * The smallest unit of time to simulate, in fractions of a millisecond.
   * Only supported by Rust simulation. */
  "timestamp-resolution-ms": number;

  // Leios Protocol Configuration
  "leios-variant": LeiosVariant;
  "leios-stage-length-slots": bigint;
  "leios-stage-active-voting-slots": bigint;
  /**
   * Determines whether a Leios pipeline has separate Vote (Send) and Vote (Recv) stages.
   * If this is set to `true`, it is recommended to set `leios-stage-active-voting-slots`
   * to be equal to `leios-stage-length-slots`.
   *
   * Only supported by Haskell simulation. */
  "leios-vote-send-recv-stages": boolean;
  /**
   * Extends Leios so that EB producers include IBs directly from previous pipelines.
   * Due to casuality, the EB must always include them, even if those IBs end up being
   * certified in their own pipeline.
   */
  "leios-late-ib-inclusion": boolean;
  /**
   * The expected time it takes a header to fully diffuse across the network.
   * This is Δhdr from the Leios paper.
   * */
  "leios-header-diffusion-time-ms": number;
  /**
   * The expected time it takes a node to generate an IB.
   * This is used as part of a validation rule to protect against equivocation attacks.
   * In practice, it should probably always equal ib-generation-cpu-time-ms.
   */
  "leios-ib-generation-time-ms": number;
  /**
   * The strategy to use when selecting TXs from the Leios mempool.
   */
  "leios-mempool-sampling-strategy": MempoolSamplingStrategy;
  /**
   * If true, transactions will be removed from the Leios mempool if they conflict with in-flight IBs.
   */
  "leios-mempool-aggressive-pruning": boolean;
  /**
   * Praos blockchain quality parameter.
   * This is η from the Leios paper.
   * Controls the pipelines EBs should reference in Full leios:
   *   i - ⌈3η/L⌉, …, i-3
   * where i is the index of the current pipeline.
   * */
  "praos-chain-quality": number;
  /**
   * If true, RBs will contain transactions directly as well as through a certificate.
   * If false, RBs will only contain a cert.
   */
  "praos-fallback-enabled": boolean;

  // Linear Leios specific configuration
  /**
   * How long the EB voting stage is allowed to last.
   * Should be more than 3x leios-header-diffusion-time-ms.
   * Matches L_vote from the paper.
   */
  "linear-vote-stage-length-slots": bigint;

  /**
   * How long after the EB voting stage are votes allowed to diffuse.
   * Matches L_diff from the paper.
   */
  "linear-diffuse-stage-length-slots": bigint;

  // Transaction Configuration
  /** Only supported by Rust simulation. */
  "tx-generation-distribution": Distribution;
  /** Only supported by Rust simulation. */
  "tx-size-bytes-distribution": Distribution;
  /**
   * Distribution used to choose the "over-collateralization factor" for a transaction.
   * An "overcollateralization factor" of n means the TX has enough collateral to be included in n+1 shards.
   * A factor of 0 means the TX has enough collateral to be include in 1 shard; i.e. it is not over-collateralized.
   * Only supported by Rust simulation.  */
  "tx-overcollateralization-factor-distribution": Distribution;
  /** Only supported by Rust simulation. */
  "tx-validation-cpu-time-ms": number;
  /** Only supported by Rust simulation. */
  "tx-max-size-bytes": bigint;
  /**
   * What fraction of TXs (from 0 to 1) should introduce conflicts with transactions which were produced before?
   * Only supported by Rust simulation.  */
  "tx-conflict-fraction": number | null;
  /**
   * When the first transaction should appear.
   * Only supported by Rust simulation.  */
  "tx-start-time"?: number | null;
  /**
   * The cutoff time after which transactions should not appear.
   * Only supported by Rust simulation.  */
  "tx-stop-time"?: number | null;

  // Ranking Block Configuration
  "rb-generation-probability": number;
  "rb-generation-cpu-time-ms": number;
  "rb-head-validation-cpu-time-ms": number;
  "rb-head-size-bytes": bigint;
  "rb-body-max-size-bytes": bigint;
  "rb-body-legacy-praos-payload-validation-cpu-time-ms-constant": number;
  "rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte": number;
  "rb-body-legacy-praos-payload-avg-size-bytes": bigint;

  // Input Block Configuration
  "ib-generation-probability": number;
  "ib-generation-cpu-time-ms": number;
  /**
   * The total number of shards available for IBs.
   * Must be divisible by ib_shard_group_count.

   * Only supported by Rust simulation. */
  "ib-shards": number;
  /**
   * The "m" IB sharding parameter.
   * Controls how many slots in a row will use the same list of shards.
   * 
   * Only supported by Rust simulation. */
  "ib-shard-period-length-slots": number;
  /**
   * The "k" IB sharding parameter.
   * Controls how many groups of shards are assigned at a time.

   * Only supported by Rust simulation. */
  "ib-shard-group-count": number;
  "ib-head-size-bytes": bigint;
  "ib-head-validation-cpu-time-ms": number;
  "ib-body-validation-cpu-time-ms-constant": number;
  "ib-body-validation-cpu-time-ms-per-byte": number;
  "ib-body-avg-size-bytes": bigint;
  /** Only supported by Rust simulation. */
  "ib-body-max-size-bytes": bigint;
  "ib-diffusion-strategy": DiffusionStrategy;
  /** Only supported by Haskell simulation. */
  "ib-diffusion-max-window-size": bigint;
  /** Only supported by Haskell simulation. */
  "ib-diffusion-max-headers-to-request": bigint;
  "ib-diffusion-max-bodies-to-request": bigint;

  // Endorsement Block Configuration
  "eb-generation-probability": number;
  "eb-generation-cpu-time-ms": number;
  "eb-validation-cpu-time-ms": number;
  "eb-header-validation-cpu-time-ms": number;
  "eb-body-validation-cpu-time-ms-constant": number;
  "eb-body-validation-cpu-time-ms-per-byte": number;
  "eb-size-bytes-constant": bigint;
  "eb-size-bytes-per-ib": bigint;
  "eb-body-avg-size-bytes": bigint;
  /** For stracciatella: when creating a new EB, have it reference transactions from a previous EB */
  "eb-include-txs-from-previous-stage": boolean

  /** Only supported by Haskell simulation. */
  "eb-diffusion-strategy": DiffusionStrategy;
  /** Only supported by Haskell simulation. */
  "eb-diffusion-max-window-size": bigint;
  /** Only supported by Haskell simulation. */
  "eb-diffusion-max-headers-to-request": bigint;
  /** Only supported by Haskell simulation. */
  "eb-diffusion-max-bodies-to-request": bigint;

  /**
   * The maximum age of EBs included in RBs.
   *
   * An EB from slot `s` can only be included in RBs
   * up to slot `s+eb-max-age-slots`.
   *
   * In short leios we expect votes to diffuse within 3 stages lengths of
   * EB generation, we allow for 2 more stage lengths to account for
   * variance in the interval within RBs.
   */
  "eb-max-age-slots": bigint;

  /**
   * The maximum age of EBs to be relayed.
   *
   * An EB from slot `s` will only be relayed
   * up to slot `s+eb-max-age-for-relay-slots`.
   *
   * Only supported by Haskell simulation.
   */
  "eb-max-age-for-relay-slots": bigint;

  /**
   * The maximum size of transactions (in bytes) which an EB can reference.
   * Only relevant when running with the "full-without-ibs" variant.
   * 
   * Only supported by Rust simulation.
   */
  "eb-referenced-txs-max-size-bytes": bigint;

  // Vote Configuration
  "vote-generation-probability": number;
  "vote-generation-cpu-time-ms-constant": number;
  "vote-generation-cpu-time-ms-per-ib": number;
  "vote-generation-cpu-time-ms-per-tx": number;
  "vote-validation-cpu-time-ms": number;
  "vote-threshold": bigint;
  "vote-bundle-size-bytes-constant": bigint;
  "vote-bundle-size-bytes-per-eb": bigint;
  /** Only supported by Haskell simulation. */
  "vote-diffusion-strategy": DiffusionStrategy;
  /** Only supported by Haskell simulation. */
  "vote-diffusion-max-window-size": bigint;
  /** Only supported by Haskell simulation. */
  "vote-diffusion-max-headers-to-request": bigint;
  /** Only supported by Haskell simulation. */
  "vote-diffusion-max-bodies-to-request": bigint;

  // Certificate Configuration
  "cert-generation-cpu-time-ms-constant": number;
  "cert-generation-cpu-time-ms-per-node": number;
  "cert-validation-cpu-time-ms-constant": number;
  "cert-validation-cpu-time-ms-per-node": number;
  "cert-size-bytes-constant": bigint;
  "cert-size-bytes-per-node": bigint;

  // Attacks
  /**
   * Configuration for a "late EB" attack,
   * where nodes deliberately withhold EBs until near the end of the voting phase.
   */
  "late-eb-attack"?: LateEBAttackConfig | null;
}

export type CleanupPolicies = "all" | CleanupPolicy[];

export type CleanupPolicy =
  | "cleanup-expired-ib"
  | "cleanup-expired-uncertified-eb"
  | "cleanup-expired-unadopted-eb"
  | "cleanup-expired-vote"
  | "cleanup-expired-certificate";

export type Distribution =
  | NormalDistribution
  | ExpDistribution
  | LogNormalDistribution
  | ConstantDistribution;

export interface NormalDistribution {
  distribution: "normal";
  mean: number;
  std_dev: number;
}

export interface ExpDistribution {
  distribution: "exp";
  lambda: number;
  scale?: number;
}

export interface LogNormalDistribution {
  distribution: "log-normal";
  mu: number;
  sigma: number;
}

export interface ConstantDistribution {
  distribution: "constant";
  value: number;
}

export enum DiffusionStrategy {
  PeerOrder = "peer-order",
  FreshestFirst = "freshest-first",
  OldestFirst = "oldest-first",
}

export enum RelayStrategy {
  RequestFromAll = "request-from-all",
  RequestFromFirst = "request-from-first",
}

export enum LeiosVariant {
  /** Short Leios: EBs only reference IBs */
  Short = "short",
  /** Full Leios: EBs reference IBs and other EBs */
  Full = "full",
  /** Full Leios Without IBs: EBs reference TXs directly, as well as other EBs */
  FullWithoutIbs = "full-without-ibs",
  /** Full Leios With TX References: IBs only contain references to TXs instead of the whole body */
  FullWithTXReferences = "full-with-tx-references",
  /** Linear Leios: Leios with as little concurrency as possible. */
  Linear = "linear",
  /** Linear Leios, but blocks include transaction references instead of full TXs */
  LinearWithTxReferences = "linear-with-tx-references",
}

export enum MempoolSamplingStrategy {
  /** Include transactions in order by ID (corresponds to generation time). */
  OrderedById = "ordered-by-id",
  /** Include transactions in random order. */
  Random = "random",
}

/**
 * Configuration for a "late EB" attack,
 * where nodes deliberately withhold EBs until near the end of the voting phase.
 */
export interface LateEBAttackConfig {
  /** The set of stake pools which are participating in the attack. */
  "attacker-nodes": string[],
  /** How long the attackers will wait before diffusing their EBs */
  "propagation-delay-ms": number,
}