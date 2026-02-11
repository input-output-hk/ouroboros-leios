export const TXID_B = 32;

export type TxIdx = number;  // compact index into global tx array

export interface GlobalTx {
  idx: number;
  txId: string;
  size_B: number;
  isAdversarial: boolean;
  honestCounterpart: number;  // idx of honest tx this front-runs (-1 if honest)
  adversarialVariant: number; // idx of adversarial variant (-1 if none created yet)
  includedInBlock: number;    // block index where this was included (-1 if not)
}

export interface Block {
  blockId: string;
  producer: number;        // node index
  clock: number;
  txIndices: number[];     // indices into global tx array
  size_B: number;
  honestCount: number;
  adversarialCount: number;
}

export interface EndorserBlock {
  ebId: string;
  producer: number;        // node index
  clock: number;
  txRefs: number[];        // indices into global tx array
  size_B: number;
}

export type TxCacheMode = 'cache-only' | 'mempool' | 'both';

export interface SimulationConfig {
  nodes: number;
  degree: number;
  blockSize_B: number;
  mempoolCapacity_B: number;
  latency_s: number;
  bandwidth_Bps: number;
  adversaries: number;
  adversaryDegree: number;
  adversaryDelay_s: number;
  txCount: number;
  txSizeMin_B: number;
  txSizeMax_B: number;
  duration_s: number;
  blockInterval_s: number;
  // Leios
  ebEnabled: boolean;
  ebSize_B: number;
  txCacheMode: TxCacheMode;
}
