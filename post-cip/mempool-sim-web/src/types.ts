export const TXID_B = 32;

export type TxId = string;

export interface Tx {
  txId: TxId;
  size_B: number;
  frontRuns: TxId;
}

export interface Block {
  blockId: string;
  producer: string;
  timestamp: number;
  transactions: Tx[];
  size_B: number;
  honestCount: number;
  adversarialCount: number;
}

export interface SimulationConfig {
  nodes: number;
  degree: number;
  block: number;
  mempool: number;
  latency: number;
  bandwidth: number;
  adversaries: number;
  adversaryDegree: number;
  txCount: number;
  txSizeMin: number;
  txSizeMax: number;
  duration: number;       // Total simulation duration in seconds
  blockInterval: number;  // Average interval between blocks (Poisson rate)
}

export const DEFAULT_CONFIG: SimulationConfig = {
  nodes: 50,
  degree: 6,
  block: 90000,
  mempool: 180000,
  latency: 0.100,
  bandwidth: 1250000,
  adversaries: 2,
  adversaryDegree: 18,
  txCount: 250,
  txSizeMin: 200,
  txSizeMax: 16384,
  duration: 20,
  blockInterval: 1,
};

export const MINIMAL_CONFIG: SimulationConfig = {
  nodes: 10,
  degree: 3,
  block: 90000,
  mempool: 180000,
  latency: 0.100,
  bandwidth: 1250000,
  adversaries: 1,
  adversaryDegree: 2,
  txCount: 50,
  txSizeMin: 200,
  txSizeMax: 16384,
  duration: 10,
  blockInterval: 2,
};

export type PresetType = 'minimal' | 'default' | 'custom';
