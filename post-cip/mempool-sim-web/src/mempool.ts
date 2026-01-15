
import type { Tx, TxId} from './types.ts'


export class MemoryPool {

  private txs: Tx[] = [];

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
    this.size_B += tx_B;
    return true;
  }

  dequeue(): Tx | undefined {
    return this.txs.shift();
  }

  peek(): Tx | undefined {
    return this.txs[0];
  }

  getSize_B(): number {
    return this.size_B;
  }

  contains(txId: TxId): boolean {
    return this.txs.filter(tx => tx.id == txId).length > 0;
  }

  get(txId: TxId): Tx | undefined {
    const matches = this.txs.filter(tx => tx.id == txId);
    if (matches.length == 0)
      return undefined;
    else
      return matches[0];
  }

  contents(): Tx[] {
    return this.txs.map(tx => tx);
  }

}
