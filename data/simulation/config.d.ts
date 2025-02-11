// This file contains TypeScript types for the configuration file formats.

/** A configuration for a Leios simulation. */
export interface Config {
  // Simulation Configuration
  "relay-strategy": RelayStrategy;
  /** Only supported by Haskell simulation. */
  "tcp-congestion-control": boolean;
  /** Only supported by Haskell simulation. */
  "multiplex-mini-protocols": boolean;

  // Leios Protocol Configuration
  "leios-stage-length-slots": bigint;
  "leios-stage-active-voting-slots": bigint;
  /**
   * Determines whether a Leios pipeline has separate Vote (Send) and Vote (Recv) stages.
   * If this is set to `true`, it is recommended to set `leios-stage-active-voting-slots`
   * to be equal to `leios-stage-length-slots`.
   *
   * Only supported by Haskell simulation. */
  "leios-vote-send-recv-stages": boolean;

  // Transaction Configuration
  /** Only supported by Rust simulation. */
  "tx-generation-distribution": Distribution;
  /** Only supported by Rust simulation. */
  "tx-size-bytes-distribution": Distribution;
  /** Only supported by Rust simulation. */
  "tx-validation-cpu-time-ms": number;
  /** Only supported by Rust simulation. */
  "tx-max-size-bytes": bigint;

  // Ranking Block Configuration
  "rb-generation-probability": number;
  "rb-generation-cpu-time-ms": number;
  "rb-head-validation-cpu-time-ms": number;
  /** Only supported by Haskell simulation. */
  "rb-head-size-bytes": bigint;
  "rb-body-max-size-bytes": bigint;
  "rb-body-legacy-praos-payload-validation-cpu-time-ms-constant": number;
  "rb-body-legacy-praos-payload-validation-cpu-time-ms-per-byte": number;
  /** Only supported by Haskell simulation. */
  "rb-body-legacy-praos-payload-avg-size-bytes": bigint;

  // Input Block Configuration
  "ib-generation-probability": number;
  "ib-generation-cpu-time-ms": number;
  /** Only supported by Haskell simulation. */
  "ib-head-size-bytes": bigint;
  "ib-head-validation-cpu-time-ms": number;
  "ib-body-validation-cpu-time-ms-constant": number;
  "ib-body-validation-cpu-time-ms-per-byte": number;
  /** Only supported by Haskell simulation. */
  "ib-body-avg-size-bytes": bigint;
  /** Only supported by Rust simulation. */
  "ib-body-max-size-bytes": bigint;
  "ib-diffusion-strategy": DiffusionStrategy;
  /** Only supported by Haskell simulation. */
  "ib-diffusion-max-window-size": bigint;
  /** Only supported by Haskell simulation. */
  "ib-diffusion-max-headers-to-request": bigint;
  /** Only supported by Haskell simulation. */
  "ib-diffusion-max-bodies-to-request": bigint;

  // Endorsement Block Configuration
  "eb-generation-probability": number;
  "eb-generation-cpu-time-ms": number;
  "eb-validation-cpu-time-ms": number;
  /** Only supported by Haskell simulation. */
  "eb-size-bytes-constant": bigint;
  /** Only supported by Haskell simulation. */
  "eb-size-bytes-per-ib": bigint;
  /** Only supported by Haskell simulation. */
  "eb-diffusion-strategy": DiffusionStrategy;
  /** Only supported by Haskell simulation. */
  "eb-diffusion-max-window-size": bigint;
  /** Only supported by Haskell simulation. */
  "eb-diffusion-max-headers-to-request": bigint;
  /** Only supported by Haskell simulation. */
  "eb-diffusion-max-bodies-to-request": bigint;

  // Vote Configuration
  "vote-generation-probability": number;
  "vote-generation-cpu-time-ms-constant": number;
  "vote-generation-cpu-time-ms-per-ib": number;
  "vote-validation-cpu-time-ms": number;
  "vote-threshold": bigint;
  /** Only supported by Haskell simulation. */
  "vote-bundle-size-bytes-constant": bigint;
  /** Only supported by Haskell simulation. */
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
  /** Only supported by Haskell simulation. */
  "cert-size-bytes-constant": bigint;
  /** Only supported by Haskell simulation. */
  "cert-size-bytes-per-node": bigint;
}

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
