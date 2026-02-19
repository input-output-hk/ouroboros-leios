// Re-export from simulation package (bitmap engine)
export {
  Simulation,
  LightNode,
  Link,
  TxRegistry,
  generateNetwork,
  addAdversaryNode,
  TXID_B,
} from 'mempool-sim-web';
export type {
  Event,
  GlobalTx,
  Block,
  EndorserBlock,
  TopologyResult,
} from 'mempool-sim-web';

// Visual types (including viz-facing config)
export * from './types';

// Layout utilities
export * from './layout';
