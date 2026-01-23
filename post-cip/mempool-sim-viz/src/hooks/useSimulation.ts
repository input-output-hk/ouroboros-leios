import { useCallback, useEffect, useRef, useState } from 'react';
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
  type HandlerEvent,
  type P2PConfig,
  DEFAULT_P2P_CONFIG,
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

interface EdgeAnimation {
  state: 'adding' | 'removing';
  progress: number;
}

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
  setP2PConfig: (config: P2PConfig) => void;
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
    progress: 0,
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
  const lastFrameTimeRef = useRef<number>(0);
  const actualDurationRef = useRef<number>(0);
  const txAnimationsRef = useRef<Map<string, AnimatedTx>>(new Map());
  const txIdCounter = useRef<number>(0);
  const isPausedRef = useRef<boolean>(false);
  const speedRef = useRef<number>(1);
  const firstFrameRef = useRef<boolean>(true);
  const initialEventsRef = useRef<number>(0);
  const forceUpdatePendingRef = useRef<boolean>(false);
  const lastEventLogLengthRef = useRef<number>(0);
  const lastFullEventLogLengthRef = useRef<number>(0);
  const lastAnimatedTxCountRef = useRef<number>(0);

  // P2P state - using refs to avoid triggering re-renders
  const p2pConfigRef = useRef<P2PConfig>(DEFAULT_P2P_CONFIG);
  const edgeAnimationsRef = useRef<Map<string, EdgeAnimation>>(new Map());
  const EDGE_ANIM_DURATION = 0.4; // 400ms

  const updateStats = useCallback(() => {
    const sim = simRef.current;
    if (!sim) return;

    const blockList = sim.blocks;
    const totalHonest = blockList.reduce((s, b) => s + b.honestCount, 0);
    const totalAdv = blockList.reduce((s, b) => s + b.adversarialCount, 0);
    const total = totalHonest + totalAdv;
    const config = configRef.current;

    // Calculate progress based on events processed (smooth) rather than time (jumpy)
    const initialEvents = initialEventsRef.current;
    const eventsProcessed = sim.eventsProcessed;
    const progress = initialEvents > 0 ? Math.min(100, (eventsProcessed / initialEvents) * 100) : 0;

    setStats({
      eventsProcessed,
      currentTime: sim.currentTime,
      progress,
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
        mempoolFillPercent: node.getFillPercent(),
        txCount: node.getTransactions().length,
        isPoisoned: node.hasAdversarialTx(),
      });
    });
    setNodes(visualNodes);
  }, []);

  // Update edges - either from static topology or dynamic P2P peers
  const updateEdges = useCallback(() => {
    const graph = graphRef.current;
    if (!graph) return;

    const currentP2PConfig = p2pConfigRef.current;

    if (!currentP2PConfig.enabled) {
      // Static mode: edges from graph topology
      const visualEdges: VisualEdge[] = [];
      graph.forEachEdge((_, _attrs, source, target) => {
        visualEdges.push({ source, target });
      });
      setEdges(visualEdges);
      return;
    }

    // P2P mode: collect edges from each node's peerManager
    const visualEdges: VisualEdge[] = [];
    const seenEdges = new Set<string>();

    graph.forEachNode((nodeId) => {
      const node = graph.getNodeAttributes(nodeId);
      const peerManager = node.getPeerManager();
      if (peerManager) {
        const peers = peerManager.getPeers();
        for (const peer of peers) {
          const edgeKey = `${peer}->${nodeId}`;
          if (!seenEdges.has(edgeKey)) {
            seenEdges.add(edgeKey);
            const animation = edgeAnimationsRef.current.get(edgeKey);
            visualEdges.push({
              source: peer,
              target: nodeId,
              animationState: animation?.state ?? 'stable',
              animationProgress: animation?.progress,
            });
          }
        }
      }
    });

    // Also include edges that are being removed (not in current peers but have removing animation)
    edgeAnimationsRef.current.forEach((anim, edgeKey) => {
      if (anim.state === 'removing' && !seenEdges.has(edgeKey)) {
        const [source, target] = edgeKey.split('->');
        if (source && target) {
          visualEdges.push({
            source,
            target,
            animationState: 'removing',
            animationProgress: anim.progress,
          });
        }
      }
    });

    setEdges(visualEdges);
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

  const handleEvent = useCallback((event: HandlerEvent) => {
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
      case 'PeerChurn': {
        const { churnResult, nodeId } = event;
        if (churnResult && (churnResult.replaced.length > 0 || churnResult.newPeers.length > 0)) {
          // Mark removed edges for fade-out animation
          for (const oldPeer of churnResult.replaced) {
            const edgeKey = `${oldPeer}->${nodeId}`;
            edgeAnimationsRef.current.set(edgeKey, { state: 'removing', progress: 0 });
          }
          // Mark added edges for fade-in animation
          for (const newPeer of churnResult.newPeers) {
            const edgeKey = `${newPeer}->${nodeId}`;
            edgeAnimationsRef.current.set(edgeKey, { state: 'adding', progress: 0 });
          }
          addLogEntry(event.clock, 'churn', `${nodeId}: -${churnResult.replaced.length} +${churnResult.newPeers.length}`);
        }
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
        safeConfig.adversaryDelay,
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
          // Throttle updates to avoid excessive re-renders during force settling
          if (!forceUpdatePendingRef.current) {
            forceUpdatePendingRef.current = true;
            requestAnimationFrame(() => {
              forceUpdatePendingRef.current = false;
              updateVisualNodes();
            });
          }
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

    // Initialize P2P if enabled
    const currentP2PConfig = p2pConfigRef.current;
    if (currentP2PConfig.enabled) {
      sim.initializeP2P(currentP2PConfig, config.duration);
    }

    // Inject transactions uniformly throughout the duration
    for (let i = 0; i < config.txCount; i++) {
      const txId = `T${i}`;
      const nodeIndex = Math.ceil(config.nodes * Math.random());
      const node = `H${nodeIndex}`;
      const time = Math.round(config.duration * Math.random());
      const size = config.txSizeMin + Math.floor(Math.random() * (config.txSizeMax - config.txSizeMin));

      sim.submitTx(time, node, {
        txId,
        size_B: size,
        frontRuns: '',
      });
    }

    // Schedule block production using Poisson process within fixed duration
    // blockInterval is the average time between blocks
    const honestNodes = Array.from({ length: config.nodes }, (_, i) => `H${i + 1}`);

    // Generate block times using exponential inter-arrival times until we exceed duration
    const blockTimes: number[] = [];
    let currentTime = 0;
    while (currentTime < config.duration) {
      // Exponential distribution: -ln(U) * mean, where U is uniform(0,1)
      const interval = -Math.log(1 - Math.random()) * config.blockInterval;
      currentTime += interval;
      if (currentTime < config.duration) {
        blockTimes.push(currentTime);
      }
    }

    // Schedule blocks with random producers
    for (const time of blockTimes) {
      const producer = honestNodes[Math.floor(Math.random() * honestNodes.length)]!;
      sim.produceBlock(time, producer, config.block);
    }

    // Duration is fixed from config
    actualDurationRef.current = config.duration;
    // Track initial event count for smooth progress calculation
    initialEventsRef.current = sim.pendingEvents;

    simRef.current = sim;
    graphRef.current = graph;
    configRef.current = config;
    txAnimationsRef.current.clear();
    edgeAnimationsRef.current.clear();
    txIdCounter.current = 0;
    eventLogRef.current = [];
    fullEventLogRef.current = [];
    logIdCounter.current = 0;
    lastBlockCountRef.current = 0;
    lastEventLogLengthRef.current = 0;
    lastFullEventLogLengthRef.current = 0;
    lastAnimatedTxCountRef.current = 0;
    setEventLog([]);
    setFullEventLog([]);

    updateVisualNodes();
    updateStats();
    setIsRunning(false);
    setIsPaused(false);
  }, [handleEvent, updateVisualNodes, updateStats, layoutType]);

  // Reinitialize simulation events without regenerating topology
  const reinitializeEvents = useCallback(() => {
    const graph = graphRef.current;
    const config = configRef.current;
    if (!graph || !config) return;

    // Reset all nodes (clears mempool, backpressure, offers, and known tx cache)
    graph.forEachNode((id) => {
      const node = graph.getNodeAttributes(id);
      node.reset(config.mempool);
    });

    // Create new simulation with existing graph
    const sim = new Simulation(graph);
    sim.setEventHandler(handleEvent);

    // Initialize P2P if enabled
    const currentP2PConfig = p2pConfigRef.current;
    if (currentP2PConfig.enabled) {
      sim.initializeP2P(currentP2PConfig, config.duration);
    }

    // Inject transactions uniformly throughout the duration
    for (let i = 0; i < config.txCount; i++) {
      const txId = `T${i}`;
      const nodeIndex = Math.ceil(config.nodes * Math.random());
      const node = `H${nodeIndex}`;
      const time = Math.round(config.duration * Math.random());
      const size = config.txSizeMin + Math.floor(Math.random() * (config.txSizeMax - config.txSizeMin));

      sim.submitTx(time, node, {
        txId,
        size_B: size,
        frontRuns: '',
      });
    }

    // Schedule block production using Poisson process within fixed duration
    const honestNodes = Array.from({ length: config.nodes }, (_, i) => `H${i + 1}`);
    const blockTimes: number[] = [];
    let currentTime = 0;
    while (currentTime < config.duration) {
      const interval = -Math.log(1 - Math.random()) * config.blockInterval;
      currentTime += interval;
      if (currentTime < config.duration) {
        blockTimes.push(currentTime);
      }
    }

    for (const time of blockTimes) {
      const producer = honestNodes[Math.floor(Math.random() * honestNodes.length)]!;
      sim.produceBlock(time, producer, config.block);
    }

    // Duration is fixed from config
    actualDurationRef.current = config.duration;
    // Track initial event count for smooth progress calculation
    initialEventsRef.current = sim.pendingEvents;

    simRef.current = sim;
    txAnimationsRef.current.clear();
    edgeAnimationsRef.current.clear();
    txIdCounter.current = 0;
    eventLogRef.current = [];
    fullEventLogRef.current = [];
    logIdCounter.current = 0;
    lastBlockCountRef.current = 0;
    lastEventLogLengthRef.current = 0;
    lastFullEventLogLengthRef.current = 0;
    lastAnimatedTxCountRef.current = 0;
    setEventLog([]);
    setFullEventLog([]);
    setBlocks([]);
    setAnimatedTxs([]);
    setBlockFlash(null);

    // Explicitly reset stats to initial values (don't rely on async updateStats)
    setStats({
      eventsProcessed: 0,
      currentTime: 0,
      progress: 0,
      blocksProduced: 0,
      totalHonestInBlocks: 0,
      totalAdversarialInBlocks: 0,
      frontRunRate: 0,
      avgBlockFillPercent: 0,
    });

    updateVisualNodes();
    setIsRunning(false);
    setIsPaused(false);
    isPausedRef.current = false;
  }, [handleEvent, updateVisualNodes]);

  // Handle layout type changes without regenerating the simulation
  useEffect(() => {
    const graph = graphRef.current;
    if (!graph) return;

    const nodeIds = graph.nodes();
    const visualEdges: VisualEdge[] = [];
    graph.forEachEdge((_, _attrs, source, target) => {
      visualEdges.push({ source, target });
    });

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
          // Throttle updates to avoid excessive re-renders during force settling
          if (!forceUpdatePendingRef.current) {
            forceUpdatePendingRef.current = true;
            requestAnimationFrame(() => {
              forceUpdatePendingRef.current = false;
              updateVisualNodes();
            });
          }
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

    updateVisualNodes();
  }, [layoutType, updateVisualNodes]);

  const animationLoop = useCallback((timestamp: number) => {
    const sim = simRef.current;
    if (!sim) {
      return;
    }

    // On first frame, just initialize timing - don't call updateStats() here.
    // reinitializeEvents() already sets correct initial stats with progress: 0.
    // Calling updateStats() again could cause timing issues with React batching.
    if (firstFrameRef.current) {
      firstFrameRef.current = false;
      lastFrameTimeRef.current = timestamp;
      animationFrameRef.current = requestAnimationFrame(animationLoop);
      return;
    }

    if (isPausedRef.current) {
      lastFrameTimeRef.current = timestamp;
      animationFrameRef.current = requestAnimationFrame(animationLoop);
      return;
    }

    const deltaMs = timestamp - lastFrameTimeRef.current;
    lastFrameTimeRef.current = timestamp;
    const deltaSec = deltaMs / 1000;

    // Process events - speed controls how many events per frame
    // At 1x: ~10 events/frame, at 10x: ~100 events/frame
    const eventsPerFrame = Math.ceil(speedRef.current * 10);
    for (let i = 0; i < eventsPerFrame && sim.pendingEvents > 0; i++) {
      sim.step();
    }

    // Log any new blocks that were created
    const currentBlocks = sim.blocks;
    while (lastBlockCountRef.current < currentBlocks.length) {
      const block = currentBlocks[lastBlockCountRef.current]!;
      addLogEntry(
        block.clock,
        'block',
        `${block.producer} → ${block.honestCount}/${block.adversarialCount} txs`
      );
      lastBlockCountRef.current++;
    }

    // Update tx animations
    const animDelta = deltaSec * speedRef.current * 2;
    txAnimationsRef.current.forEach((anim, id) => {
      anim.progress += animDelta;
      if (anim.progress >= 1) {
        txAnimationsRef.current.delete(id);
      }
    });
    // Only update animatedTxs state if count changed (avoid re-render when empty)
    const currentAnimCount = txAnimationsRef.current.size;
    if (currentAnimCount !== lastAnimatedTxCountRef.current) {
      lastAnimatedTxCountRef.current = currentAnimCount;
      setAnimatedTxs(Array.from(txAnimationsRef.current.values()));
    }

    // Update edge animations (for P2P churn)
    const edgeAnimDelta = deltaSec / EDGE_ANIM_DURATION;
    const completedEdgeAnims: string[] = [];
    edgeAnimationsRef.current.forEach((anim, edgeKey) => {
      anim.progress += edgeAnimDelta;
      if (anim.progress >= 1) {
        completedEdgeAnims.push(edgeKey);
      }
    });
    // Remove completed animations
    for (const key of completedEdgeAnims) {
      edgeAnimationsRef.current.delete(key);
    }

    // Fade block flash
    setBlockFlash(prev => {
      if (!prev) return null;
      const newOpacity = prev.opacity - deltaSec;
      if (newOpacity <= 0) return null;
      return { ...prev, opacity: newOpacity };
    });

    updateVisualNodes();
    updateStats();

    // Update edges if P2P is enabled
    if (p2pConfigRef.current.enabled) {
      updateEdges();
    }

    // Only update event logs if length changed
    const currentEventLogLength = eventLogRef.current.length;
    if (currentEventLogLength !== lastEventLogLengthRef.current) {
      lastEventLogLengthRef.current = currentEventLogLength;
      setEventLog([...eventLogRef.current]);
    }
    const currentFullEventLogLength = fullEventLogRef.current.length;
    if (currentFullEventLogLength !== lastFullEventLogLengthRef.current) {
      lastFullEventLogLengthRef.current = currentFullEventLogLength;
      setFullEventLog([...fullEventLogRef.current]);
    }

    if (sim.pendingEvents === 0) {
      txAnimationsRef.current.clear();
      setAnimatedTxs([]);
      setIsRunning(false);
    } else {
      animationFrameRef.current = requestAnimationFrame(animationLoop);
    }
  }, [updateVisualNodes, updateStats, addLogEntry, updateEdges]);

  const reset = useCallback(() => {
    if (animationFrameRef.current) {
      cancelAnimationFrame(animationFrameRef.current);
    }
    if (graphRef.current && configRef.current) {
      reinitializeEvents();
    }
  }, [reinitializeEvents]);

  const start = useCallback(() => {
    if (!simRef.current) return;

    // If simulation completed, reset first (same as pressing stop)
    if (simRef.current.pendingEvents === 0) {
      reset();
    }

    setIsRunning(true);
    setIsPaused(false);
    isPausedRef.current = false;
    firstFrameRef.current = true;
    lastFrameTimeRef.current = performance.now();
    animationFrameRef.current = requestAnimationFrame(animationLoop);
  }, [animationLoop, reset]);

  const pause = useCallback(() => {
    isPausedRef.current = true;
    setIsPaused(true);
  }, []);

  const resume = useCallback(() => {
    isPausedRef.current = false;
    setIsPaused(false);
    // Reset frame time but keep simElapsedRef (accumulated progress)
    lastFrameTimeRef.current = performance.now();
    // Ensure animation loop is running
    if (animationFrameRef.current) {
      cancelAnimationFrame(animationFrameRef.current);
    }
    animationFrameRef.current = requestAnimationFrame(animationLoop);
  }, [animationLoop]);

  const stepOnce = useCallback(() => {
    const sim = simRef.current;
    if (!sim || sim.pendingEvents === 0) return;
    sim.step();
    updateVisualNodes();
    updateStats();
    setAnimatedTxs(Array.from(txAnimationsRef.current.values()));
  }, [updateVisualNodes, updateStats]);

  const setSpeed = useCallback((newSpeed: number) => {
    speedRef.current = newSpeed;
    setSpeedState(newSpeed);
  }, []);

  // Use actual duration computed from scheduled events
  const simulationDuration = actualDurationRef.current;

  // Force layout drag handlers
  const onDragStart = useCallback((nodeId: string, x: number, y: number) => {
    if (forceLayoutRef.current) {
      forceLayoutRef.current.startDrag(nodeId, x, y);
    }
  }, []);

  const onDrag = useCallback((nodeId: string, x: number, y: number) => {
    if (forceLayoutRef.current) {
      forceLayoutRef.current.drag(nodeId, x, y);
    }
  }, []);

  const onDragEnd = useCallback((_nodeId: string) => {
    if (forceLayoutRef.current) {
      // Keep the node pinned where it was dropped - don't unpin
      // This lets users arrange the graph like an untangle puzzle
      forceLayoutRef.current.endDrag(_nodeId);
    }
  }, []);

  // Set P2P config (updates ref)
  const setP2PConfig = useCallback((config: P2PConfig) => {
    p2pConfigRef.current = config;
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
    setP2PConfig,
    onDragStart,
    onDrag,
    onDragEnd,
  };
}
