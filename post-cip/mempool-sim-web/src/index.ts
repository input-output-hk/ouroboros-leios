// Core types
export type { TxId, Tx, Block, SimulationConfig, PresetType } from './types.js';
export { TXID_B, DEFAULT_CONFIG, MINIMAL_CONFIG } from './types.js';

// Classes
export { MemoryPool } from './mempool.js';
export { Link } from './link.js';
export { Node } from './node.js';

// Simulation
export { Simulation } from './simulation.js';
export type { Event, SimulationEventHandler } from './simulation.js';

// Network generation
export { generateNetwork, addAdversaryNode } from './topology.js';

// Logger (for CLI usage)
export { logger } from './logger.js';
