// Re-export from simulation package
export {
  TXID_B,
  DEFAULT_CONFIG,
  MINIMAL_CONFIG,
  MemoryPool,
  Link,
  Node,
  Simulation,
  generateNetwork,
  addAdversaryNode,
  logger,
} from 'mempool-sim-web';
export type {
  TxId,
  Tx,
  Block,
  SimulationConfig,
  PresetType,
  Event,
  SimulationEventHandler,
} from 'mempool-sim-web';

// Visual types
export * from './types';

// Layout utilities
export * from './layout';
