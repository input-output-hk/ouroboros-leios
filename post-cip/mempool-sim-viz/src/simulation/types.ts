// Visual types for the visualization layer

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

export interface AnimatedBlock {
  id: string;
  blockId: string;
  fromNode: string;
  toNode: string;
  progress: number;
  type: 'rb' | 'eb';
}

export interface SimulationStats {
  eventsProcessed: number;
  currentTime: number;
  progress: number; // 0-100, based on events processed for smooth display
  blocksProduced: number;
  endorserBlocksProduced: number;
  totalHonestInBlocks: number;
  totalAdversarialInBlocks: number;
  frontRunRate: number;
  avgBlockFillPercent: number;
}

// --- Viz-facing simulation config ---

export interface SimulationConfig {
  nodes: number;
  degree: number;
  block: number;       // block size in bytes
  mempool: number;     // mempool capacity in bytes
  latency: number;     // latency in seconds
  bandwidth: number;   // bandwidth in bytes/sec
  adversaries: number;
  adversaryDegree: number;
  adversaryDelay: number; // in seconds
  txCount: number;
  txSizeMin: number;
  txSizeMax: number;
  duration: number;    // in seconds
  blockInterval: number; // in seconds
  // Leios
  ebEnabled: boolean;
  ebSize: number;      // EB size in bytes
  ebAnnouncementRate: number;   // 0-1
  ebCertificationRate: number;  // 0-1
  // Peer churn
  peerChurnEnabled: boolean;
  peerChurnInterval: number;    // seconds
  peerChurnRate: number;        // 0-1
}

export type PresetType = 'minimal' | 'default' | 'large' | 'custom';

export const MINIMAL_CONFIG: SimulationConfig = {
  nodes: 20,
  degree: 3,
  block: 90_112,
  mempool: 180_224,
  latency: 0.05,
  bandwidth: 12_500_000,
  adversaries: 2,
  adversaryDegree: 3,
  adversaryDelay: 0.000001,
  txCount: 100,
  txSizeMin: 300,
  txSizeMax: 1500,
  duration: 20,
  blockInterval: 3,
  ebEnabled: false,
  ebSize: 10_000_000,
  ebAnnouncementRate: 0.5,
  ebCertificationRate: 0.8,
  peerChurnEnabled: false,
  peerChurnInterval: 5,
  peerChurnRate: 0.05,
};

export const DEFAULT_CONFIG: SimulationConfig = {
  nodes: 50,
  degree: 4,
  block: 90_112,
  mempool: 180_224,
  latency: 0.05,
  bandwidth: 12_500_000,
  adversaries: 5,
  adversaryDegree: 10,
  adversaryDelay: 0.000001,
  txCount: 250,
  txSizeMin: 300,
  txSizeMax: 1500,
  duration: 30,
  blockInterval: 3,
  ebEnabled: false,
  ebSize: 10_000_000,
  ebAnnouncementRate: 0.5,
  ebCertificationRate: 0.8,
  peerChurnEnabled: false,
  peerChurnInterval: 5,
  peerChurnRate: 0.05,
};

export const LARGE_CONFIG: SimulationConfig = {
  nodes: 500,
  degree: 6,
  block: 90_112,
  mempool: 180_224,
  latency: 0.05,
  bandwidth: 12_500_000,
  adversaries: 10,
  adversaryDegree: 10,
  adversaryDelay: 0.000001,
  txCount: 1000,
  txSizeMin: 300,
  txSizeMax: 1500,
  duration: 60,
  blockInterval: 3,
  ebEnabled: false,
  ebSize: 10_000_000,
  ebAnnouncementRate: 0.5,
  ebCertificationRate: 0.8,
  peerChurnEnabled: false,
  peerChurnInterval: 5,
  peerChurnRate: 0.05,
};

// Display-friendly block type (producer as string name)
export interface BlockDisplay {
  blockId: string;
  producer: string;
  clock: number;
  honestCount: number;
  adversarialCount: number;
  size_B: number;
}

