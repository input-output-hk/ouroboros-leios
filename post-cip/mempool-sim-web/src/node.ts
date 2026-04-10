/**
 * Lightweight node — no tx storage, just counters + references to global bitmaps.
 */
export class LightNode {
  readonly idx: number;
  readonly id: string;       // "H1", "A1" etc for logging
  readonly honest: boolean;
  readonly frontrunDelay_s: number;
  mempoolBytes: number = 0;
  readonly mempoolCapacity_B: number;

  // Upstream peer indices (in-edges: peers that send TO this node)
  upstreamPeers: number[] = [];
  // Downstream peer indices (out-edges: peers this node sends TO)
  downstreamPeers: number[] = [];

  // Block/EB dedup
  seenBlocks: Set<string> = new Set();
  seenEBs: Set<string> = new Set();

  // Arrival order of txs accepted into mempool.
  // Values are tx indices, with -1 marking removed entries.
  private mempoolTxOrder: number[] = [];
  private mempoolTxPos: Map<number, number> = new Map();
  private mempoolTxHead = 0;

  constructor(idx: number, id: string, honest: boolean, frontrunDelay_s: number, mempoolCapacity_B: number) {
    this.idx = idx;
    this.id = id;
    this.honest = honest;
    this.frontrunDelay_s = frontrunDelay_s;
    this.mempoolCapacity_B = mempoolCapacity_B;
  }

  canFitTx(size_B: number): boolean {
    return this.mempoolBytes + size_B <= this.mempoolCapacity_B;
  }

  addToMempool(size_B: number): void {
    this.mempoolBytes += size_B;
  }

  removeFromMempool(size_B: number): void {
    this.mempoolBytes = Math.max(0, this.mempoolBytes - size_B);
  }

  addTxToOrder(txIdx: number): void {
    if (this.mempoolTxPos.has(txIdx)) return;
    this.mempoolTxPos.set(txIdx, this.mempoolTxOrder.length);
    this.mempoolTxOrder.push(txIdx);
  }

  removeTxFromOrder(txIdx: number): void {
    const pos = this.mempoolTxPos.get(txIdx);
    if (pos === undefined) return;
    this.mempoolTxOrder[pos] = -1;
    this.mempoolTxPos.delete(txIdx);
    this.advanceTxOrderHead();
  }

  scanTxOrder(visitor: (txIdx: number) => boolean): void {
    this.advanceTxOrderHead();
    for (let i = this.mempoolTxHead; i < this.mempoolTxOrder.length; i++) {
      const txIdx = this.mempoolTxOrder[i]!;
      if (txIdx < 0) continue;
      if (!visitor(txIdx)) break;
    }
  }

  hasTxInOrder(txIdx: number): boolean {
    return this.mempoolTxPos.has(txIdx);
  }

  private advanceTxOrderHead(): void {
    while (this.mempoolTxHead < this.mempoolTxOrder.length && this.mempoolTxOrder[this.mempoolTxHead] === -1) {
      this.mempoolTxHead++;
    }
  }

  reset(): void {
    this.mempoolBytes = 0;
    this.seenBlocks.clear();
    this.seenEBs.clear();
    this.mempoolTxOrder = [];
    this.mempoolTxPos.clear();
    this.mempoolTxHead = 0;
  }
}
