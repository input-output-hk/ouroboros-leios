import { MemoryPool } from './mempool.js';

export const TXID_B = 32;

export type TxId = string; 

export interface Tx {
  id: TxId;
  size_B: number;
  honest: boolean;
}
