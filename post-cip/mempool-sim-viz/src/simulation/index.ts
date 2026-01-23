// Re-export from simulation package
export {
  TXID_B,
  DEFAULT_CONFIG,
  MINIMAL_CONFIG,
  DEFAULT_P2P_CONFIG,
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
  P2PConfig,
  ChurnResult,
  Event,
  HandlerEvent,
  PeerChurnEvent,
  SimulationEventHandler,
} from 'mempool-sim-web';

// Visual types
export * from './types';

// Layout utilities
export * from './layout';
