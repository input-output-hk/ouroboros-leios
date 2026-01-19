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
  txDuration: number;
  txSizeMin: number;
  txSizeMax: number;
  slotDuration: number;
  slots: number;
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
  txDuration: 20,
  txSizeMin: 200,
  txSizeMax: 16384,
  slotDuration: 1,
  slots: 20,
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
  txDuration: 4,
  txSizeMin: 200,
  txSizeMax: 16384,
  slotDuration: 1,
  slots: 5,
};

export type PresetType = 'minimal' | 'default' | 'custom';

export interface NodePosition {
  x: number;
  y: number;
}

export interface VisualNode {
  id: string;
  honest: boolean;
  position: NodePosition;
  mempoolFillPercent: number;
  txCount: number;
  isPoisoned: boolean;
}

export interface VisualEdge {
  source: string;
  target: string;
}

export interface AnimatedTx {
  id: string;
  txId: string;
  fromNode: string;
  toNode: string;
  progress: number;
  isAdversarial: boolean;
}

export interface SimulationStats {
  eventsProcessed: number;
  currentTime: number;
  blocksProduced: number;
  totalHonestInBlocks: number;
  totalAdversarialInBlocks: number;
  frontRunRate: number;
  avgBlockFillPercent: number;
}
