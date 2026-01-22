import { logger } from './logger.js';

/**
 * Result of a churn operation, for logging purposes.
 */
export interface ChurnResult {
  replaced: string[];
  newPeers: string[];
}

/**
 * PeerManager implements P2P peer selection with dynamic topology churn.
 * Each node maintains connections to its degree peers, but those peers
 * can change over time as churn replaces some with new random peers.
 */
export class PeerManager {
  private readonly nodeId: string;
  private currentPeers: Set<string> = new Set();  // Currently connected peers
  private initialPeers: string[] = [];             // Initial peers for reset
  private allNodes: string[] = [];                 // All possible peers in network
  private churnProbability: number;

  constructor(nodeId: string, churnProbability: number) {
    this.nodeId = nodeId;
    this.churnProbability = churnProbability;
  }

  /**
   * Initialize peer tracking.
   * @param initialPeers The initial set of peers from topology
   * @param allNodes All nodes in the network (for selecting new peers during churn)
   */
  initialize(initialPeers: string[], allNodes: string[]): void {
    this.initialPeers = [...initialPeers];
    this.currentPeers = new Set(initialPeers);
    // Exclude self from potential peers
    this.allNodes = allNodes.filter(n => n !== this.nodeId);

    logger.debug({
      node: this.nodeId,
      peers: Array.from(this.currentPeers),
      totalNetworkNodes: this.allNodes.length,
    }, 'P2P initialized');
  }

  /**
   * Run a churn cycle: randomly replace some peers with new random ones.
   * Each peer has churnProbability chance of being replaced.
   * Returns the list of replaced and new peers for logging.
   */
  churn(): ChurnResult {
    const result: ChurnResult = { replaced: [], newPeers: [] };

    // Get potential new peers (nodes not currently connected)
    const availablePeers = this.allNodes.filter(p => !this.currentPeers.has(p));
    const shuffledAvailable = this.shuffle([...availablePeers]);
    let availableIndex = 0;

    // For each current peer, potentially replace it
    const peers = Array.from(this.currentPeers);
    for (const peer of peers) {
      if (Math.random() < this.churnProbability && availableIndex < shuffledAvailable.length) {
        // Replace this peer with a new random one
        this.currentPeers.delete(peer);
        const newPeer = shuffledAvailable[availableIndex]!;
        this.currentPeers.add(newPeer);
        result.replaced.push(peer);
        result.newPeers.push(newPeer);
        availableIndex++;
      }
    }

    if (result.replaced.length > 0) {
      logger.debug({
        node: this.nodeId,
        replaced: result.replaced,
        newPeers: result.newPeers,
        peerCount: this.currentPeers.size,
      }, 'P2P churn');
    }

    return result;
  }

  /**
   * Get all current peers for transaction propagation.
   */
  getPeers(): string[] {
    return Array.from(this.currentPeers);
  }

  /**
   * Fisher-Yates shuffle for random peer selection.
   */
  private shuffle<T>(array: T[]): T[] {
    for (let i = array.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [array[i], array[j]] = [array[j]!, array[i]!];
    }
    return array;
  }

  /**
   * Reset peer states (for simulation restart).
   */
  reset(): void {
    this.currentPeers = new Set(this.initialPeers);
  }
}
