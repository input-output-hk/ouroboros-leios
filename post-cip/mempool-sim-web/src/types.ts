import { MemoryPool } from './mempool.js';

export const TXID_B = 32;

export type TxId = string; 

export interface Tx {
  txId: TxId;
  size_B: number;
  frontRuns: TxId;
}
