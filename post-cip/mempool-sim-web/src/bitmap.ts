/**
 * Compact bitset backed by Uint32Array.
 * One bit per node — supports 10k+ nodes efficiently.
 */
export class BitSet {
  private words: Uint32Array;
  readonly size: number;

  constructor(size: number) {
    this.size = size;
    this.words = new Uint32Array(Math.ceil(size / 32));
  }

  set(idx: number): void {
    const w = idx >>> 5;
    this.words[w] = this.words[w]! | (1 << (idx & 31));
  }

  get(idx: number): boolean {
    return (this.words[idx >>> 5]! & (1 << (idx & 31))) !== 0;
  }

  clear(idx: number): void {
    const w = idx >>> 5;
    this.words[w] = this.words[w]! & ~(1 << (idx & 31));
  }

  reset(): void {
    this.words.fill(0);
  }

  /** Count of set bits (popcount) */
  count(): number {
    let c = 0;
    for (let i = 0; i < this.words.length; i++) {
      let v = this.words[i]!;
      v = v - ((v >>> 1) & 0x55555555);
      v = (v & 0x33333333) + ((v >>> 2) & 0x33333333);
      c += (((v + (v >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24;
    }
    return c;
  }

  /** Iterate over set bit indices, calling fn for each */
  forEach(fn: (idx: number) => void): void {
    for (let w = 0; w < this.words.length; w++) {
      let bits = this.words[w]!;
      while (bits !== 0) {
        const bit = bits & (-bits);        // lowest set bit
        const bitIdx = (w << 5) + (31 - Math.clz32(bit));
        fn(bitIdx);
        bits ^= bit;
      }
    }
  }
}
