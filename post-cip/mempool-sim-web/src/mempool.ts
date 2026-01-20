
import type { Tx, TxId} from './types.ts'


export class MemoryPool {

  // Ordered queue of transactions (FIFO for block production)
  private txs: Tx[] = [];

  // Index for O(1) lookups by txId
  private txMap: Map<TxId, Tx> = new Map();

  private size_B: number;

  public readonly capacity_B: number;

  constructor(capacity_B: number) {
    this.size_B = 0;
    this.capacity_B = capacity_B;
  }

  enqueue(tx: Tx, tx_B: number): boolean {
    if (this.size_B + tx_B > this.capacity_B) {
      return false;
    }
    this.txs.push(tx);
    this.txMap.set(tx.txId, tx);
    this.size_B += tx_B;
    return true;
  }

  dequeue(): Tx | undefined {
    const tx = this.txs.shift();
    if (tx) {
      this.txMap.delete(tx.txId);
      this.size_B -= tx.size_B;
    }
    return tx;
  }

  peek(): Tx | undefined {
    return this.txs[0];
  }

  getSize_B(): number {
    return this.size_B;
  }

  contains(txId: TxId): boolean {
    return this.txMap.has(txId);
  }

  get(txId: TxId): Tx | undefined {
    return this.txMap.get(txId);
  }

  contents(): Tx[] {
    return [...this.txs];
  }

  // Get count of transactions in the mempool
  count(): number {
    return this.txs.length;
  }

  // Get fill percentage (for visualization)
  getFillPercent(): number {
    return this.capacity_B > 0 ? (this.size_B / this.capacity_B) * 100 : 0;
  }

  // Remove a transaction by ID (for block confirmation propagation)
  remove(txId: TxId): boolean {
    const tx = this.txMap.get(txId);
    if (!tx) return false;
    this.txMap.delete(txId);
    const idx = this.txs.findIndex(t => t.txId === txId);
    if (idx >= 0) {
      this.txs.splice(idx, 1);
      this.size_B -= tx.size_B;
    }
    return true;
  }

}
