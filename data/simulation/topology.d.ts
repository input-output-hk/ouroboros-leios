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
