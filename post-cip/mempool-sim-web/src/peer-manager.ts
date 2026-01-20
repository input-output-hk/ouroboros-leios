import { logger } from './logger.js';

/**
 * Result of a churn operation, for logging purposes.
 */
export interface ChurnResult {
  replaced: string[];
  newPeers: string[];
}

/**
 * PeerManager implements a simplified P2P peer selection with an "active set" model.
 * Each node maintains a subset of active peers from its topology for tx propagation.
 * Periodic churn randomly replaces some active peers with inactive ones.
 */
export class PeerManager {
  private readonly nodeId: string;
  private allPeers: string[] = [];           // All upstream peers from topology
  private activePeers: Set<string> = new Set();  // Currently active subset
  private targetActive: number;
  private churnProbability: number;

  constructor(nodeId: string, targetActive: number, churnProbability: number) {
    this.nodeId = nodeId;
    this.targetActive = targetActive;
    this.churnProbability = churnProbability;
  }

  /**
   * Initialize peer tracking from the graph topology.
   * Stores all upstream peers and bootstraps the active set.
   */
  initialize(upstreamPeers: string[]): void {
    this.allPeers = [...upstreamPeers];
    this.bootstrap();
  }

  /**
   * Bootstrap the active set by randomly selecting targetActive peers.
   */
  private bootstrap(): void {
    this.activePeers.clear();
    const shuffled = this.shuffle([...this.allPeers]);
    const count = Math.min(this.targetActive, shuffled.length);

    for (let i = 0; i < count; i++) {
      this.activePeers.add(shuffled[i]!);
    }

    logger.debug({
      node: this.nodeId,
      activePeers: Array.from(this.activePeers),
      totalPeers: this.allPeers.length,
    }, 'P2P bootstrap complete');
  }

  /**
   * Run a churn cycle: randomly replace some active peers with inactive ones.
   * Each active peer has churnProbability chance of being replaced.
   * Returns the list of replaced and new peers for logging.
   */
  churn(): ChurnResult {
    const result: ChurnResult = { replaced: [], newPeers: [] };

    // Get inactive peers (peers not currently in active set)
    const inactivePeers = this.allPeers.filter(p => !this.activePeers.has(p));
    const shuffledInactive = this.shuffle([...inactivePeers]);
    let inactiveIndex = 0;

    // For each active peer, potentially replace it
    const currentActive = Array.from(this.activePeers);
    for (const peer of currentActive) {
      if (Math.random() < this.churnProbability && inactiveIndex < shuffledInactive.length) {
        // Replace this peer
        this.activePeers.delete(peer);
        const newPeer = shuffledInactive[inactiveIndex]!;
        this.activePeers.add(newPeer);
        result.replaced.push(peer);
        result.newPeers.push(newPeer);
        inactiveIndex++;
      }
    }

    // Backfill if we're below target (can happen if topology has fewer peers)
    while (this.activePeers.size < this.targetActive && inactiveIndex < shuffledInactive.length) {
      const newPeer = shuffledInactive[inactiveIndex]!;
      this.activePeers.add(newPeer);
      result.newPeers.push(newPeer);
      inactiveIndex++;
    }

    if (result.replaced.length > 0 || result.newPeers.length > 0) {
      logger.debug({
        node: this.nodeId,
        replaced: result.replaced,
        newPeers: result.newPeers,
        activeCount: this.activePeers.size,
        totalPeers: this.allPeers.length,
      }, 'P2P churn');
    }

    return result;
  }

  /**
   * Get all currently active peers for transaction propagation.
   */
  getActivePeers(): string[] {
    return Array.from(this.activePeers);
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
    this.activePeers.clear();
    this.bootstrap();
  }
}
