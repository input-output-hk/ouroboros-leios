// This file contains TypeScript types for the configuration file formats.

/**
 * The topology for a Leios simulation.
 *
 * The nodes in a topology may either specify their location as cluster names,
 * which may be omitted, or as coordinates, but all nodes in the topology must
 * use the same kind of location.
 */
export interface Topology {
  nodes:
  | {
    [name: NodeName]: Node<Cluster>;
  }
  | {
    [name: NodeName]: Node<Coord2D>;
  };
}

/** A node. */
export interface Node<Location> {
  stake?: bigint | null;
  "cpu-core-count"?: bigint | null;
  location: Location;
  producers: { [producer: NodeName]: LinkInfo };
  /**
   * What fraction of TXs (from 0 to 1) should introduce conflicts with transactions which were produced before?
   * Only supported by Rust simulation.  */
  "tx-conflict-fraction"?: number | null;
  /**
   * How likely is this node to generate transactions, compared to its peers?
   * Default is 0 for nodes with stake, 1 for nodes with no stake.
   * Only supported by Rust simulation.
   */
  "tx-generation-weight"?: number | null;
  /** If not null, the node will behave according to the given Behaviour.
  *
  * Only supported by Haskell simulation.
  */
  adversarial?: Behaviour | null;
}

/** Link information. */
export interface LinkInfo {
  "latency-ms": number;
  "bandwidth-bytes-per-second"?: bigint | null;
}

export type NodeName = string;

export interface Cluster {
  cluster?: string;
}

export type Coord2D = [number, number];

export type Behaviour =
  | UnboundedIbs
  ;

/** A node that after some time stops respecting IB sortition and
instead starts generating old IBs every slot.

Only supported by Haskell simulation.
*/
export interface UnboundedIbs {
  behaviour: "unbounded-ibs";
  /* When to start the adversarial generation. */
  "starting-at-slot": number;
  "slot-of-generated-ibs": number;
  "ibs-per-slot": number;
}
