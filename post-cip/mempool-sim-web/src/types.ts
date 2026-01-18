import { MemoryPool } from './mempool.js';

export const TXID_B = 32;

export type TxId = string;

export interface Tx {
  txId: TxId;
  size_B: number;
  frontRuns: TxId;
}

export interface Block {
  blockId: string;           // "B0", "B1", ...
  producer: string;          // node ID
  timestamp: number;         // simulation clock
  transactions: Tx[];        // included txs
  size_B: number;            // total bytes
  honestCount: number;       // frontRuns === ""
  adversarialCount: number;  // frontRuns !== ""
}
