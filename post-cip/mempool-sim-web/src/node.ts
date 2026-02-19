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

  reset(): void {
    this.mempoolBytes = 0;
    this.seenBlocks.clear();
    this.seenEBs.clear();
  }
}
