import { BitSet } from './bitmap.js';
import type { GlobalTx } from './types.js';

/**
 * Global transaction registry. All txs stored once.
 * Per-tx bitmaps track which nodes have seen / have in mempool.
 */
export class TxRegistry {
  readonly txs: GlobalTx[] = [];
  readonly nodeCount: number;

  // Per-tx bitmaps
  readonly inMempool: BitSet[] = [];   // node has tx in mempool
  readonly known: BitSet[] = [];       // node has seen tx (offered/received)
  readonly inCache: BitSet[] = [];     // node has tx in EB cache

  constructor(nodeCount: number) {
    this.nodeCount = nodeCount;
  }

  register(txId: string, size_B: number, isAdversarial: boolean, honestCounterpart: number): number {
    const idx = this.txs.length;
    this.txs.push({
      idx,
      txId,
      size_B,
      isAdversarial,
      honestCounterpart,
      adversarialVariant: -1,
      includedInBlock: -1,
    });
    this.inMempool.push(new BitSet(this.nodeCount));
    this.known.push(new BitSet(this.nodeCount));
    this.inCache.push(new BitSet(this.nodeCount));
    return idx;
  }

  /** Check if node has seen a conflicting counterpart of this tx */
  hasConflict(txIdx: number, nodeIdx: number): boolean {
    const tx = this.txs[txIdx]!;
    if (tx.isAdversarial) {
      return tx.honestCounterpart >= 0 && this.known[tx.honestCounterpart]!.get(nodeIdx);
    } else {
      return tx.adversarialVariant >= 0 && this.known[tx.adversarialVariant]!.get(nodeIdx);
    }
  }
}
