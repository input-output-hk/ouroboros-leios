import { MemoryPool } from './mempool.js';

export type TxId = string; 

export interface Tx {
  id: TxId;
  size_b: number;
  honest: boolean;
}

export interface Node {
  honest: boolean;
  mempool: MemoryPool<TxId>;
}

export interface Link {
  latency_s: number;
  bandwidth_bps: number;
}
