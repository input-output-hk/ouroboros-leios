export const OVERHEAD_B: number = 80;

export class Link {
  public readonly latency_s: number;
  public readonly bandwidth_Bps: number;

  constructor(latency_s: number, bandwidth_Bps: number) {
    this.latency_s = latency_s;
    this.bandwidth_Bps = bandwidth_Bps;
  }

  computeDelay(now: number, size_B: number): number {
    const jitter: number = Math.random() / 1e9;
    return now + this.latency_s + (OVERHEAD_B + size_B) / this.bandwidth_Bps + jitter;
  }
}
