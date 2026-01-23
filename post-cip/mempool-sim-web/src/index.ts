// Core types
export type { TxId, Tx, Block, SimulationConfig, PresetType, P2PConfig } from './types.js';
export { TXID_B, DEFAULT_CONFIG, MINIMAL_CONFIG, DEFAULT_P2P_CONFIG } from './types.js';

// P2P Peer Manager
export { PeerManager } from './peer-manager.js';
export type { ChurnResult } from './peer-manager.js';

// Classes
export { MemoryPool } from './mempool.js';
export { Link } from './link.js';
export { Node } from './node.js';

// Simulation
export { Simulation } from './simulation.js';
export type { Event, HandlerEvent, PeerChurnEvent, SimulationEventHandler } from './simulation.js';

// Network generation
export { generateNetwork, addAdversaryNode } from './topology.js';

// Logger (for CLI usage)
export { logger } from './logger.js';
