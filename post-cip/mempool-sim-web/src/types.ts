import { MemoryPool } from './mempool.js';

export type TxId = string; 

export interface Tx {
  id: TxId;
  size_B: number;
  honest: boolean;
}
