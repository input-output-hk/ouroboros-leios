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
  animationState?: 'stable' | 'adding' | 'removing';
  animationProgress?: number;
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
  progress: number; // 0-100, based on events processed for smooth display
  blocksProduced: number;
  totalHonestInBlocks: number;
  totalAdversarialInBlocks: number;
  frontRunRate: number;
  avgBlockFillPercent: number;
}
