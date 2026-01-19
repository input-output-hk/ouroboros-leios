import { useCallback, useRef, useState } from 'react';
import { DirectedGraph } from 'graphology';
import {
  Simulation,
  generateNetwork,
  addAdversaryNode,
  type SimulationConfig,
  type Block,
  type SimulationStats,
  type VisualNode,
  type VisualEdge,
  type AnimatedTx,
  type Event,
  type LayoutType,
  Node,
  Link,
} from '@/simulation';
import { computeCircularLayout, createForceLayout, type ForceLayoutController } from '@/simulation/layout';

export interface LogEntry {
  id: number;
  time: number;
  kind: string;
  message: string;
  isAdversarial?: boolean;
}

const MAX_LOG_ENTRIES = 100;

interface UseSimulationReturn {
  isRunning: boolean;
  isPaused: boolean;
  speed: number;
  stats: SimulationStats;
  simulationDuration: number;
  nodes: VisualNode[];
  edges: VisualEdge[];
  animatedTxs: AnimatedTx[];
  blocks: Block[];
  blockFlash: { nodeId: string; opacity: number } | null;
  eventLog: LogEntry[];
  fullEventLog: LogEntry[];
  initialize: (config: SimulationConfig) => void;
  start: () => void;
  pause: () => void;
  resume: () => void;
  reset: () => void;
  step: () => void;
  setSpeed: (speed: number) => void;
  onDragStart: (nodeId: string, x: number, y: number) => void;
  onDrag: (nodeId: string, x: number, y: number) => void;
  onDragEnd: (nodeId: string) => void;
}

export function useSimulation(layoutType: LayoutType = 'circular'): UseSimulationReturn {
  const [isRunning, setIsRunning] = useState(false);
  const [isPaused, setIsPaused] = useState(false);
  const [speed, setSpeedState] = useState(1);
  const [stats, setStats] = useState<SimulationStats>({
    eventsProcessed: 0,
    currentTime: 0,
    blocksProduced: 0,
    totalHonestInBlocks: 0,
    totalAdversarialInBlocks: 0,
    frontRunRate: 0,
    avgBlockFillPercent: 0,
  });
  const [nodes, setNodes] = useState<VisualNode[]>([]);
  const [edges, setEdges] = useState<VisualEdge[]>([]);
  const [animatedTxs, setAnimatedTxs] = useState<AnimatedTx[]>([]);
  const [blocks, setBlocks] = useState<Block[]>([]);
  const [blockFlash, setBlockFlash] = useState<{ nodeId: string; opacity: number } | null>(null);
  const [eventLog, setEventLog] = useState<LogEntry[]>([]);
  const [fullEventLog, setFullEventLog] = useState<LogEntry[]>([]);

  const simRef = useRef<Simulation | null>(null);
  const eventLogRef = useRef<LogEntry[]>([]);
  const fullEventLogRef = useRef<LogEntry[]>([]);
  const logIdCounter = useRef<number>(0);
  const lastBlockCountRef = useRef<number>(0);
  const forceLayoutRef = useRef<ForceLayoutController | null>(null);
  const graphRef = useRef<DirectedGraph<Node, Link> | null>(null);
  const configRef = useRef<SimulationConfig | null>(null);
  const positionsRef = useRef<Map<string, { x: number; y: number }>>(new Map());
  const animationFrameRef = useRef<number | null>(null);
  const lastTimeRef = useRef<number>(0);
  const txAnimationsRef = useRef<Map<string, AnimatedTx>>(new Map());
  const txIdCounter = useRef<number>(0);

  const updateStats = useCallback(() => {
    const sim = simRef.current;
    if (!sim) return;

    const blockList = sim.blocks;
    const totalHonest = blockList.reduce((s, b) => s + b.honestCount, 0);
    const totalAdv = blockList.reduce((s, b) => s + b.adversarialCount, 0);
    const total = totalHonest + totalAdv;
    const config = configRef.current;

    setStats({
      eventsProcessed: sim.eventsProcessed,
      currentTime: sim.currentTime,
      blocksProduced: blockList.length,
      totalHonestInBlocks: totalHonest,
      totalAdversarialInBlocks: totalAdv,
      frontRunRate: total > 0 ? totalAdv / total : 0,
      avgBlockFillPercent: blockList.length > 0 && config
        ? (blockList.reduce((s, b) => s + b.size_B, 0) / (blockList.length * config.block)) * 100
        : 0,
    });
    setBlocks([...blockList]);
  }, []);

  const updateVisualNodes = useCallback(() => {
    const graph = graphRef.current;
    if (!graph) return;

    const visualNodes: VisualNode[] = [];
    graph.forEachNode((id) => {
      const node = graph.getNodeAttributes(id);
      const pos = positionsRef.current.get(id) || { x: 0, y: 0 };
      visualNodes.push({
        id,
        honest: node.honest,
        position: pos,
        mempoolFillPercent: node.getMempoolFillPercent(),
        txCount: node.getMempoolTxCount(),
        isPoisoned: node.hasAdversarialTx(),
      });
    });
    setNodes(visualNodes);
  }, []);

  const addLogEntry = useCallback((time: number, kind: string, message: string, isAdversarial?: boolean) => {
    const entry: LogEntry = {
      id: logIdCounter.current++,
      time,
      kind,
      message,
      isAdversarial,
    };
    // Add to full log (no limit)
    fullEventLogRef.current.push(entry);
    // Add to display log (limited)
    eventLogRef.current.push(entry);
    if (eventLogRef.current.length > MAX_LOG_ENTRIES) {
      eventLogRef.current.shift();
    }
  }, []);

  const handleEvent = useCallback((event: Event) => {
    const graph = graphRef.current;
    if (!graph) return;

    // Log the event (blocks are logged separately after creation to include contents)
    switch (event.kind) {
      case 'SubmitTx': {
        const isAdv = event.tx.frontRuns !== '';
        addLogEntry(event.clock, 'submit', `${event.tx.txId} → ${event.to}`, isAdv);
        break;
      }
      case 'SendTx': {
        const isAdv = event.tx.frontRuns !== '';
        addLogEntry(event.clock, 'send', `${event.tx.txId}: ${event.from} → ${event.to}`, isAdv);
        break;
      }
    }

    if (event.kind === 'SendTx') {
      const fromPos = positionsRef.current.get(event.from);
      const toPos = positionsRef.current.get(event.to);
      if (fromPos && toPos) {
        const animId = `tx-${txIdCounter.current++}`;
        const isAdversarial = event.tx.frontRuns !== '';
        txAnimationsRef.current.set(animId, {
          id: animId,
          txId: event.tx.txId,
          fromNode: event.from,
          toNode: event.to,
          progress: 0,
          isAdversarial,
        });
      }
    } else if (event.kind === 'ProduceBlock') {
      setBlockFlash({ nodeId: event.producer, opacity: 1 });
    }
  }, [addLogEntry]);

  const initialize = useCallback((config: SimulationConfig) => {
    // Validate and clamp config values to prevent errors
    const safeConfig = {
      ...config,
      degree: Math.min(config.degree, config.nodes - 1),
      adversaryDegree: Math.min(config.adversaryDegree, config.nodes),
    };

    // Generate network
    const graph = generateNetwork(
      safeConfig.nodes,
      safeConfig.degree,
      safeConfig.mempool,
      safeConfig.latency,
      safeConfig.bandwidth
    );

    // Add adversary nodes
    for (let i = 0; i < safeConfig.adversaries; i++) {
      addAdversaryNode(
        graph,
        `A${i + 1}`,
        safeConfig.adversaryDegree,
        safeConfig.adversaryDegree,
        safeConfig.mempool,
        safeConfig.latency,
        safeConfig.bandwidth
      );
    }

    // Extract edges first (needed for force layout)
    const visualEdges: VisualEdge[] = [];
    graph.forEachEdge((_, _attrs, source, target) => {
      visualEdges.push({ source, target });
    });
    setEdges(visualEdges);

    // Compute layout based on type
    const nodeIds = graph.nodes();
    if (layoutType === 'force') {
      // Stop any existing force layout
      if (forceLayoutRef.current) {
        forceLayoutRef.current.stop();
      }
      // Create new force layout
      const forceLayout = createForceLayout(
        nodeIds,
        visualEdges,
        600,
        600,
        (positions) => {
          positionsRef.current = positions;
          updateVisualNodes();
        }
      );
      forceLayoutRef.current = forceLayout;
      positionsRef.current = forceLayout.getPositions();
    } else {
      // Stop any existing force layout
      if (forceLayoutRef.current) {
        forceLayoutRef.current.stop();
        forceLayoutRef.current = null;
      }
      positionsRef.current = computeCircularLayout(nodeIds, 600, 600);
    }

    // Create simulation
    const sim = new Simulation(graph);
    sim.setEventHandler(handleEvent);

    // Inject transactions
    for (let i = 0; i < config.txCount; i++) {
      const txId = `T${i}`;
      const nodeIndex = Math.ceil(config.nodes * Math.random());
      const node = `H${nodeIndex}`;
      const time = Math.round(config.txDuration * Math.random());
      const size = config.txSizeMin + Math.floor(Math.random() * (config.txSizeMax - config.txSizeMin));

      sim.submitTx(time, node, {
        txId,
        size_B: size,
        frontRuns: '',
      });
    }

    // Schedule block production
    const honestNodes = Array.from({ length: config.nodes }, (_, i) => `H${i + 1}`);
    for (let slot = 0; slot < config.slots; slot++) {
      const producer = honestNodes[slot % honestNodes.length]!;
      sim.produceBlock(slot * config.slotDuration, producer, config.block);
    }

    simRef.current = sim;
    graphRef.current = graph;
    configRef.current = config;
    txAnimationsRef.current.clear();
    txIdCounter.current = 0;
    eventLogRef.current = [];
    fullEventLogRef.current = [];
    logIdCounter.current = 0;
    lastBlockCountRef.current = 0;
    setEventLog([]);
    setFullEventLog([]);

    updateVisualNodes();
    updateStats();
    setIsRunning(false);
    setIsPaused(false);
  }, [handleEvent, updateVisualNodes, updateStats, layoutType]);

  const animationLoop = useCallback((timestamp: number) => {
    const sim = simRef.current;
    if (!sim || isPaused) {
      animationFrameRef.current = requestAnimationFrame(animationLoop);
      return;
    }

    const deltaMs = timestamp - lastTimeRef.current;
    lastTimeRef.current = timestamp;

    // Process simulation events based on speed
    const eventsPerFrame = Math.ceil(speed * 10);
    for (let i = 0; i < eventsPerFrame && sim.pendingEvents > 0; i++) {
      sim.step();
    }

    // Log any new blocks that were created
    const currentBlocks = sim.blocks;
    while (lastBlockCountRef.current < currentBlocks.length) {
      const block = currentBlocks[lastBlockCountRef.current]!;
      const honestCount = block.honestCount;
      const advCount = block.adversarialCount;
      addLogEntry(
        block.timestamp,
        'block',
        `${block.producer} → ${honestCount}/${advCount} txs`
      );
      lastBlockCountRef.current++;
    }

    // Update tx animations
    const animDelta = (deltaMs / 1000) * speed * 2;
    txAnimationsRef.current.forEach((anim, id) => {
      anim.progress += animDelta;
      if (anim.progress >= 1) {
        txAnimationsRef.current.delete(id);
      }
    });
    setAnimatedTxs(Array.from(txAnimationsRef.current.values()));

    // Fade block flash over 1 second (real time, not sim time)
    setBlockFlash(prev => {
      if (!prev) return null;
      const fadeRate = deltaMs / 1000; // 1 second fade
      const newOpacity = prev.opacity - fadeRate;
      if (newOpacity <= 0) return null;
      return { ...prev, opacity: newOpacity };
    });

    updateVisualNodes();
    updateStats();
    // Sync event logs from refs to state
    setEventLog([...eventLogRef.current]);
    setFullEventLog([...fullEventLogRef.current]);

    if (sim.pendingEvents === 0) {
      // Clear any remaining tx animations when simulation ends
      txAnimationsRef.current.clear();
      setAnimatedTxs([]);
      setIsRunning(false);
    } else {
      animationFrameRef.current = requestAnimationFrame(animationLoop);
    }
  }, [isPaused, speed, updateVisualNodes, updateStats, addLogEntry]);

  const start = useCallback(() => {
    if (!simRef.current) return;

    // If simulation completed, re-initialize with same config
    if (simRef.current.pendingEvents === 0 && configRef.current) {
      initialize(configRef.current);
    }

    setIsRunning(true);
    setIsPaused(false);
    lastTimeRef.current = performance.now();
    animationFrameRef.current = requestAnimationFrame(animationLoop);
  }, [animationLoop, initialize]);

  const pause = useCallback(() => {
    setIsPaused(true);
  }, []);

  const resume = useCallback(() => {
    setIsPaused(false);
    lastTimeRef.current = performance.now();
  }, []);

  const reset = useCallback(() => {
    if (animationFrameRef.current) {
      cancelAnimationFrame(animationFrameRef.current);
    }
    if (configRef.current) {
      initialize(configRef.current);
    }
  }, [initialize]);

  const stepOnce = useCallback(() => {
    const sim = simRef.current;
    if (!sim || sim.pendingEvents === 0) return;
    sim.step();
    updateVisualNodes();
    updateStats();
    setAnimatedTxs(Array.from(txAnimationsRef.current.values()));
  }, [updateVisualNodes, updateStats]);

  const setSpeed = useCallback((newSpeed: number) => {
    setSpeedState(newSpeed);
  }, []);

  // Calculate simulation duration from config
  const simulationDuration = configRef.current
    ? configRef.current.slots * configRef.current.slotDuration
    : 0;

  // Force layout drag handlers
  const onDragStart = useCallback((nodeId: string, _x: number, _y: number) => {
    if (forceLayoutRef.current) {
      forceLayoutRef.current.fixNode(nodeId);
    }
  }, []);

  const onDrag = useCallback((nodeId: string, x: number, y: number) => {
    if (forceLayoutRef.current) {
      forceLayoutRef.current.dragNode(nodeId, x, y);
    }
  }, []);

  const onDragEnd = useCallback((nodeId: string) => {
    if (forceLayoutRef.current) {
      forceLayoutRef.current.unfixNode(nodeId);
    }
  }, []);

  return {
    isRunning,
    isPaused,
    speed,
    stats,
    simulationDuration,
    nodes,
    edges,
    animatedTxs,
    blocks,
    blockFlash,
    eventLog,
    fullEventLog,
    initialize,
    start,
    pause,
    resume,
    reset,
    step: stepOnce,
    setSpeed,
    onDragStart,
    onDrag,
    onDragEnd,
  };
}
