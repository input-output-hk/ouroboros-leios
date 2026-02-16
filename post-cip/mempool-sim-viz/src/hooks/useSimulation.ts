import { useCallback, useEffect, useRef, useState } from 'react';
import {
  Simulation,
  LightNode,
  Link,
  generateNetwork,
  addAdversaryNode,
  type Event,
  type EndorserBlock,
  type SimulationConfig,
  type SimulationStats,
  type VisualNode,
  type VisualEdge,
  type AnimatedTx,
  type AnimatedBlock,
  type BlockDisplay,
  type CacheTxInfo,
  type LayoutType,
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
  animatedBlocks: AnimatedBlock[];
  blocks: BlockDisplay[];
  endorserBlocks: EndorserBlock[];
  blockFlash: { nodeId: string; opacity: number } | null;
  eventLog: LogEntry[];
  fullEventLog: LogEntry[];
  initialize: (config: SimulationConfig) => void;
  applyConfig: (config: SimulationConfig) => void;
  start: () => void;
  pause: () => void;
  resume: () => void;
  reset: () => void;
  step: () => void;
  setSpeed: (speed: number) => void;
  getSelectedNodeCache: (nodeIdx: number) => CacheTxInfo[];
  onDragStart: (nodeId: string, x: number, y: number) => void;
  onDrag: (nodeId: string, x: number, y: number) => void;
  onDragEnd: (nodeId: string) => void;
  getSimRef: () => Simulation | null;
  nodeOrder: number[];
  honestCount: number;
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
    endorserBlocksProduced: 0,
    totalHonestInBlocks: 0,
    totalAdversarialInBlocks: 0,
    frontRunRate: 0,
    avgBlockFillPercent: 0,
  });
  const [nodes, setNodes] = useState<VisualNode[]>([]);
  const [edges, setEdges] = useState<VisualEdge[]>([]);
  const [animatedTxs, setAnimatedTxs] = useState<AnimatedTx[]>([]);
  const [animatedBlocks, setAnimatedBlocks] = useState<AnimatedBlock[]>([]);
  const [blocks, setBlocks] = useState<BlockDisplay[]>([]);
  const [endorserBlocks, setEndorserBlocks] = useState<EndorserBlock[]>([]);
  const [blockFlash, setBlockFlash] = useState<{ nodeId: string; opacity: number } | null>(null);
  const [eventLog, setEventLog] = useState<LogEntry[]>([]);
  const [fullEventLog, setFullEventLog] = useState<LogEntry[]>([]);
  const [nodeOrder, setNodeOrder] = useState<number[]>([]);
  const [honestNodeCount, setHonestNodeCount] = useState(0);

  const simRef = useRef<Simulation | null>(null);
  const nodesRef = useRef<LightNode[]>([]);
  const linksRef = useRef<Map<string, Link>>(new Map());
  const eventLogRef = useRef<LogEntry[]>([]);
  const fullEventLogRef = useRef<LogEntry[]>([]);
  const logIdCounter = useRef<number>(0);
  const lastBlockCountRef = useRef<number>(0);
  const lastEBCountRef = useRef<number>(0);
  const forceLayoutRef = useRef<ForceLayoutController | null>(null);
  const configRef = useRef<SimulationConfig | null>(null);
  const positionsRef = useRef<Map<string, { x: number; y: number }>>(new Map());
  const animationFrameRef = useRef<number | null>(null);
  const lastFrameTimeRef = useRef<number>(0);
  const actualDurationRef = useRef<number>(0);
  const txAnimationsRef = useRef<Map<string, AnimatedTx>>(new Map());
  const blockAnimationsRef = useRef<Map<string, AnimatedBlock>>(new Map());
  const txIdCounter = useRef<number>(0);
  const blockAnimCounter = useRef<number>(0);
  const isPausedRef = useRef<boolean>(false);
  const speedRef = useRef<number>(1);
  const firstFrameRef = useRef<boolean>(true);
  const initialEventsRef = useRef<number>(0);
  const forceUpdatePendingRef = useRef<boolean>(false);
  const layoutTypeRef = useRef<LayoutType>(layoutType);
  const lastEventLogLengthRef = useRef<number>(0);
  const lastFullEventLogLengthRef = useRef<number>(0);
  const lastAnimatedTxCountRef = useRef<number>(0);
  const lastAnimatedBlockCountRef = useRef<number>(0);

  const updateStats = useCallback(() => {
    const sim = simRef.current;
    if (!sim) return;

    const blockList = sim.blocks;
    const totalHonest = blockList.reduce((s, b) => s + b.honestCount, 0);
    const totalAdv = blockList.reduce((s, b) => s + b.adversarialCount, 0);
    const total = totalHonest + totalAdv;
    const config = configRef.current;

    const initialEvents = initialEventsRef.current;
    const eventsProcessed = sim.eventsProcessed;
    const progress = initialEvents > 0 ? Math.min(100, (eventsProcessed / initialEvents) * 100) : 0;

    const nodeList = nodesRef.current;
    setStats({
      eventsProcessed,
      currentTime: sim.currentTime,
      progress,
      blocksProduced: blockList.length,
      endorserBlocksProduced: sim.endorserBlocks.length,
      totalHonestInBlocks: totalHonest,
      totalAdversarialInBlocks: totalAdv,
      frontRunRate: total > 0 ? totalAdv / total : 0,
      avgBlockFillPercent: blockList.length > 0 && config
        ? (blockList.reduce((s, b) => s + b.size_B, 0) / (blockList.length * config.block)) * 100
        : 0,
    });
    // Convert blocks to display format (producer index → node ID string)
    setBlocks(blockList.map(b => ({
      blockId: b.blockId,
      producer: nodeList[b.producer]?.id ?? `#${b.producer}`,
      clock: b.clock,
      honestCount: b.honestCount,
      adversarialCount: b.adversarialCount,
      size_B: b.size_B,
    })));
  }, []);

  const updateVisualNodes = useCallback(() => {
    const sim = simRef.current;
    const nodeList = nodesRef.current;
    if (!sim || nodeList.length === 0) return;

    const visualNodes: VisualNode[] = nodeList.map(node => {
      const pos = positionsRef.current.get(node.id) || { x: 0, y: 0 };
      return {
        id: node.id,
        honest: node.honest,
        position: pos,
        mempoolFillPercent: sim.getNodeFillPercent(node.idx),
        txCount: sim.getNodeTxCount(node.idx),
        isPoisoned: sim.isNodePoisoned(node.idx),
        cacheCount: sim.getNodeCacheCount(node.idx),
      };
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
    fullEventLogRef.current.push(entry);
    eventLogRef.current.push(entry);
    if (eventLogRef.current.length > MAX_LOG_ENTRIES) {
      eventLogRef.current.shift();
    }
  }, []);

  const buildEdges = useCallback((): VisualEdge[] => {
    const nodeList = nodesRef.current;
    const linkMap = linksRef.current;
    const visualEdges: VisualEdge[] = [];

    linkMap.forEach((_, key) => {
      const parts = key.split('-');
      const fromIdx = parseInt(parts[0]!, 10);
      const toIdx = parseInt(parts[1]!, 10);
      const fromName = nodeList[fromIdx]?.id;
      const toName = nodeList[toIdx]?.id;
      if (fromName && toName) {
        visualEdges.push({ source: fromName, target: toName });
      }
    });

    return visualEdges;
  }, []);

  const processSimEvent = useCallback((event: Event) => {
    const nodeList = nodesRef.current;

    switch (event.kind) {
      case 'SubmitTx': {
        const sim = simRef.current;
        if (!sim) break;
        const tx = sim.registry.txs[event.txIdx]!;
        const nodeName = nodeList[event.nodeIdx]?.id ?? `#${event.nodeIdx}`;
        addLogEntry(event.clock, 'submit', `${tx.txId} → ${nodeName}`, tx.isAdversarial);
        break;
      }

      case 'SendTx': {
        const sim = simRef.current;
        if (!sim) break;
        const tx = sim.registry.txs[event.txIdx]!;
        const fromName = nodeList[event.from]?.id ?? `#${event.from}`;
        const toName = nodeList[event.to]?.id ?? `#${event.to}`;
        addLogEntry(event.clock, 'send', `${tx.txId}: ${fromName} → ${toName}`, tx.isAdversarial);

        // Create tx animation (skip in matrix mode)
        if (layoutTypeRef.current !== 'matrix') {
          const fromPos = positionsRef.current.get(fromName);
          const toPos = positionsRef.current.get(toName);
          if (fromPos && toPos) {
            const animId = `tx-${txIdCounter.current++}`;
            txAnimationsRef.current.set(animId, {
              id: animId,
              txId: tx.txId,
              fromNode: fromName,
              toNode: toName,
              progress: 0,
              isAdversarial: tx.isAdversarial,
            });
          }
        }
        break;
      }

      case 'ProduceBlock': {
        const producerName = nodeList[event.producerIdx]?.id ?? `#${event.producerIdx}`;
        setBlockFlash({ nodeId: producerName, opacity: 1 });
        break;
      }

      case 'DiffuseBlock': {
        const fromName = nodeList[event.from]?.id ?? `#${event.from}`;
        const toName = nodeList[event.to]?.id ?? `#${event.to}`;
        const sim = simRef.current;
        const blockId = sim ? sim.blocks[event.blockIdx]?.blockId ?? `B${event.blockIdx}` : `B${event.blockIdx}`;
        addLogEntry(event.clock, 'diffuse-rb', `${blockId}: ${fromName} → ${toName}`);

        if (layoutTypeRef.current !== 'matrix') {
          const fromPos = positionsRef.current.get(fromName);
          const toPos = positionsRef.current.get(toName);
          if (fromPos && toPos) {
            const animId = `rb-${blockAnimCounter.current++}`;
            blockAnimationsRef.current.set(animId, {
              id: animId,
              blockId,
              fromNode: fromName,
              toNode: toName,
              progress: 0,
              type: 'rb',
            });
          }
        }
        break;
      }

      case 'DiffuseEB': {
        const fromName = nodeList[event.from]?.id ?? `#${event.from}`;
        const toName = nodeList[event.to]?.id ?? `#${event.to}`;
        const sim = simRef.current;
        const ebId = sim ? sim.endorserBlocks[event.ebIdx]?.ebId ?? `EB${event.ebIdx}` : `EB${event.ebIdx}`;
        addLogEntry(event.clock, 'diffuse-eb', `${ebId}: ${fromName} → ${toName}`);

        if (layoutTypeRef.current !== 'matrix') {
          const fromPos = positionsRef.current.get(fromName);
          const toPos = positionsRef.current.get(toName);
          if (fromPos && toPos) {
            const animId = `eb-${blockAnimCounter.current++}`;
            blockAnimationsRef.current.set(animId, {
              id: animId,
              blockId: ebId,
              fromNode: fromName,
              toNode: toName,
              progress: 0,
              type: 'eb',
            });
          }
        }
        break;
      }

      case 'SendEBTx': {
        const sim = simRef.current;
        if (!sim) break;
        const tx = sim.registry.txs[event.txIdx]!;
        const fromName = nodeList[event.from]?.id ?? `#${event.from}`;
        const toName = nodeList[event.to]?.id ?? `#${event.to}`;
        addLogEntry(event.clock, 'eb-tx', `${tx.txId}: ${fromName} → ${toName}`);

        if (layoutTypeRef.current !== 'matrix') {
          const fromPos = positionsRef.current.get(fromName);
          const toPos = positionsRef.current.get(toName);
          if (fromPos && toPos) {
            const animId = `tx-${txIdCounter.current++}`;
            txAnimationsRef.current.set(animId, {
              id: animId,
              txId: tx.txId,
              fromNode: fromName,
              toNode: toName,
              progress: 0,
              isAdversarial: tx.isAdversarial,
            });
          }
        }
        break;
      }

      case 'PeerChurn': {
        addLogEntry(event.clock, 'churn', 'Edge swap');
        // In graph mode, rebuild edges
        if (layoutTypeRef.current !== 'matrix') {
          setEdges(buildEdges());
        }
        break;
      }
    }
  }, [addLogEntry, buildEdges]);

  const initialize = useCallback((config: SimulationConfig) => {
    // Validate and clamp config values
    const safeConfig = {
      ...config,
      degree: Math.min(config.degree, config.nodes - 1),
      adversaryDegree: Math.min(config.adversaryDegree, config.nodes),
    };

    // Generate network using bitmap engine
    const { nodes: lightNodes, links } = generateNetwork(
      safeConfig.nodes,
      safeConfig.degree,
      safeConfig.mempool,
      safeConfig.latency,
      safeConfig.bandwidth,
    );

    // Add adversary nodes
    for (let i = 0; i < safeConfig.adversaries; i++) {
      addAdversaryNode(
        lightNodes,
        links,
        safeConfig.adversaryDegree,
        safeConfig.adversaryDegree,
        safeConfig.adversaryDelay,
        safeConfig.mempool,
        safeConfig.latency,
        safeConfig.bandwidth,
      );
    }

    // Store refs
    nodesRef.current = lightNodes;
    linksRef.current = links;

    // Build edges from links Map
    const visualEdges = buildEdges();
    setEdges(visualEdges);

    // Compute layout (skip for matrix mode — no node positions needed)
    if (layoutType !== 'matrix') {
      const nodeIds = lightNodes.map(n => n.id);
      if (layoutType === 'force') {
        if (forceLayoutRef.current) {
          forceLayoutRef.current.stop();
        }
        const forceLayout = createForceLayout(
          nodeIds,
          visualEdges,
          600,
          600,
          (positions) => {
            positionsRef.current = positions;
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
        if (forceLayoutRef.current) {
          forceLayoutRef.current.stop();
          forceLayoutRef.current = null;
        }
        positionsRef.current = computeCircularLayout(nodeIds, 600, 600);
      }
    } else {
      if (forceLayoutRef.current) {
        forceLayoutRef.current.stop();
        forceLayoutRef.current = null;
      }
    }

    // Create simulation
    const sim = new Simulation(lightNodes, links);
    sim.ebEnabled = safeConfig.ebEnabled;
    sim.ebSize_B = safeConfig.ebSize;
    sim.txCacheMode = safeConfig.txCacheMode;
    sim.ebAnnouncementRate = safeConfig.ebAnnouncementRate;
    sim.ebCertificationRate = safeConfig.ebCertificationRate;
    sim.peerChurnEnabled = safeConfig.peerChurnEnabled;
    sim.peerChurnInterval_s = safeConfig.peerChurnInterval;
    sim.peerChurnRate = safeConfig.peerChurnRate;

    // Inject transactions
    for (let i = 0; i < safeConfig.txCount; i++) {
      const txId = `T${i}`;
      const nodeIndex = Math.floor(Math.random() * safeConfig.nodes);
      const time = Math.round(safeConfig.duration * Math.random());
      const size = safeConfig.txSizeMin + Math.floor(Math.random() * (safeConfig.txSizeMax - safeConfig.txSizeMin));
      sim.submitTx(time, nodeIndex, txId, size);
    }

    // Schedule block production using Poisson process
    const blockTimes: number[] = [];
    let currentTime = 0;
    while (currentTime < safeConfig.duration) {
      const interval = -Math.log(1 - Math.random()) * safeConfig.blockInterval;
      currentTime += interval;
      if (currentTime < safeConfig.duration) {
        blockTimes.push(currentTime);
      }
    }

    for (const time of blockTimes) {
      const producerIdx = Math.floor(Math.random() * safeConfig.nodes);
      sim.produceBlock(time, producerIdx, safeConfig.block);
    }

    // Schedule peer churn if enabled
    if (safeConfig.peerChurnEnabled) {
      sim.schedulePeerChurn(0);
    }

    actualDurationRef.current = safeConfig.duration;
    initialEventsRef.current = sim.pendingEvents;

    simRef.current = sim;
    configRef.current = safeConfig;
    setNodeOrder(sim.getNodeOrder());
    setHonestNodeCount(sim.honestCount);
    txAnimationsRef.current.clear();
    blockAnimationsRef.current.clear();
    txIdCounter.current = 0;
    blockAnimCounter.current = 0;
    eventLogRef.current = [];
    fullEventLogRef.current = [];
    logIdCounter.current = 0;
    lastBlockCountRef.current = 0;
    lastEBCountRef.current = 0;
    lastEventLogLengthRef.current = 0;
    lastFullEventLogLengthRef.current = 0;
    lastAnimatedTxCountRef.current = 0;
    lastAnimatedBlockCountRef.current = 0;
    setEventLog([]);
    setFullEventLog([]);
    setEndorserBlocks([]);

    updateVisualNodes();
    updateStats();
    setIsRunning(false);
    setIsPaused(false);
  }, [updateVisualNodes, updateStats, layoutType, buildEdges]);

  // Reinitialize simulation events without regenerating topology
  const reinitializeEvents = useCallback(() => {
    const nodeList = nodesRef.current;
    const linkMap = linksRef.current;
    const config = configRef.current;
    if (nodeList.length === 0 || !config) return;

    // Reset all nodes
    for (const node of nodeList) {
      node.reset();
    }

    // Create new simulation with existing topology
    const sim = new Simulation(nodeList, linkMap);
    sim.ebEnabled = config.ebEnabled;
    sim.ebSize_B = config.ebSize;
    sim.txCacheMode = config.txCacheMode;
    sim.ebAnnouncementRate = config.ebAnnouncementRate;
    sim.ebCertificationRate = config.ebCertificationRate;
    sim.peerChurnEnabled = config.peerChurnEnabled;
    sim.peerChurnInterval_s = config.peerChurnInterval;
    sim.peerChurnRate = config.peerChurnRate;

    // Inject transactions
    for (let i = 0; i < config.txCount; i++) {
      const txId = `T${i}`;
      const nodeIndex = Math.floor(Math.random() * config.nodes);
      const time = Math.round(config.duration * Math.random());
      const size = config.txSizeMin + Math.floor(Math.random() * (config.txSizeMax - config.txSizeMin));
      sim.submitTx(time, nodeIndex, txId, size);
    }

    // Schedule block production
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
      const producerIdx = Math.floor(Math.random() * config.nodes);
      sim.produceBlock(time, producerIdx, config.block);
    }

    // Schedule peer churn if enabled
    if (config.peerChurnEnabled) {
      sim.schedulePeerChurn(0);
    }

    actualDurationRef.current = config.duration;
    initialEventsRef.current = sim.pendingEvents;

    simRef.current = sim;
    txAnimationsRef.current.clear();
    blockAnimationsRef.current.clear();
    txIdCounter.current = 0;
    blockAnimCounter.current = 0;
    eventLogRef.current = [];
    fullEventLogRef.current = [];
    logIdCounter.current = 0;
    lastBlockCountRef.current = 0;
    lastEBCountRef.current = 0;
    lastEventLogLengthRef.current = 0;
    lastFullEventLogLengthRef.current = 0;
    lastAnimatedTxCountRef.current = 0;
    lastAnimatedBlockCountRef.current = 0;
    setEventLog([]);
    setFullEventLog([]);
    setBlocks([]);
    setAnimatedTxs([]);
    setAnimatedBlocks([]);
    setBlockFlash(null);
    setEndorserBlocks([]);

    setStats({
      eventsProcessed: 0,
      currentTime: 0,
      progress: 0,
      blocksProduced: 0,
      endorserBlocksProduced: 0,
      totalHonestInBlocks: 0,
      totalAdversarialInBlocks: 0,
      frontRunRate: 0,
      avgBlockFillPercent: 0,
    });

    updateVisualNodes();
    setIsRunning(false);
    setIsPaused(false);
    isPausedRef.current = false;
  }, [updateVisualNodes]);

  // Apply a new config without regenerating topology — updates configRef and reinitializes events
  const applyConfig = useCallback((config: SimulationConfig) => {
    configRef.current = config;
    reinitializeEvents();
  }, [reinitializeEvents]);

  // Keep layout type ref in sync
  useEffect(() => {
    layoutTypeRef.current = layoutType;
  }, [layoutType]);

  // Handle layout type changes without regenerating the simulation
  useEffect(() => {
    const nodeList = nodesRef.current;
    if (nodeList.length === 0) return;

    const nodeIds = nodeList.map(n => n.id);
    const visualEdges = buildEdges();

    if (layoutType === 'force') {
      if (forceLayoutRef.current) {
        forceLayoutRef.current.stop();
      }
      const forceLayout = createForceLayout(
        nodeIds,
        visualEdges,
        600,
        600,
        (positions) => {
          positionsRef.current = positions;
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
      if (forceLayoutRef.current) {
        forceLayoutRef.current.stop();
        forceLayoutRef.current = null;
      }
      positionsRef.current = computeCircularLayout(nodeIds, 600, 600);
    }

    updateVisualNodes();
  }, [layoutType, updateVisualNodes, buildEdges]);

  const animationLoop = useCallback((timestamp: number) => {
    const sim = simRef.current;
    if (!sim) return;

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

    // Process events — scale up for large networks
    const isMatrixMode = layoutType === 'matrix';
    const nodeCount = nodesRef.current.length;
    const baseEvents = Math.ceil(speedRef.current * 10);
    const eventsPerFrame = nodeCount > 500 ? baseEvents * 100 : baseEvents;
    for (let i = 0; i < eventsPerFrame && sim.pendingEvents > 0; i++) {
      const event = sim.step();
      if (event) {
        processSimEvent(event);
      }
    }

    // Log any new blocks
    const currentBlocks = sim.blocks;
    const nodeList = nodesRef.current;
    while (lastBlockCountRef.current < currentBlocks.length) {
      const block = currentBlocks[lastBlockCountRef.current]!;
      const producerName = nodeList[block.producer]?.id ?? `#${block.producer}`;
      addLogEntry(
        block.clock,
        'block',
        `${producerName} → ${block.honestCount}/${block.adversarialCount} txs`
      );
      lastBlockCountRef.current++;
    }

    // Track new endorser blocks
    if (sim.endorserBlocks.length > lastEBCountRef.current) {
      lastEBCountRef.current = sim.endorserBlocks.length;
      setEndorserBlocks([...sim.endorserBlocks]);
    }

    if (!isMatrixMode) {
      // Update tx animations
      const animDelta = deltaSec * speedRef.current * 2;
      txAnimationsRef.current.forEach((anim, id) => {
        anim.progress += animDelta;
        if (anim.progress >= 1) {
          txAnimationsRef.current.delete(id);
        }
      });
      const currentAnimCount = txAnimationsRef.current.size;
      if (currentAnimCount !== lastAnimatedTxCountRef.current) {
        lastAnimatedTxCountRef.current = currentAnimCount;
        setAnimatedTxs(Array.from(txAnimationsRef.current.values()));
      }

      // Update block/EB animations (slightly slower than tx)
      const blockAnimDelta = deltaSec * speedRef.current * 1.5;
      blockAnimationsRef.current.forEach((anim, id) => {
        anim.progress += blockAnimDelta;
        if (anim.progress >= 1) {
          blockAnimationsRef.current.delete(id);
        }
      });
      const currentBlockAnimCount = blockAnimationsRef.current.size;
      if (currentBlockAnimCount !== lastAnimatedBlockCountRef.current) {
        lastAnimatedBlockCountRef.current = currentBlockAnimCount;
        setAnimatedBlocks(Array.from(blockAnimationsRef.current.values()));
      }

      updateVisualNodes();
    }

    // Fade block flash
    setBlockFlash(prev => {
      if (!prev) return null;
      const newOpacity = prev.opacity - deltaSec;
      if (newOpacity <= 0) return null;
      return { ...prev, opacity: newOpacity };
    });

    updateStats();

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
      blockAnimationsRef.current.clear();
      setAnimatedTxs([]);
      setAnimatedBlocks([]);
      setIsRunning(false);
    } else {
      animationFrameRef.current = requestAnimationFrame(animationLoop);
    }
  }, [updateVisualNodes, updateStats, addLogEntry, processSimEvent]);

  const reset = useCallback(() => {
    if (animationFrameRef.current) {
      cancelAnimationFrame(animationFrameRef.current);
    }
    if (nodesRef.current.length > 0 && configRef.current) {
      reinitializeEvents();
    }
  }, [reinitializeEvents]);

  const start = useCallback(() => {
    if (!simRef.current) return;

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
    lastFrameTimeRef.current = performance.now();
    if (animationFrameRef.current) {
      cancelAnimationFrame(animationFrameRef.current);
    }
    animationFrameRef.current = requestAnimationFrame(animationLoop);
  }, [animationLoop]);

  const stepOnce = useCallback(() => {
    const sim = simRef.current;
    if (!sim || sim.pendingEvents === 0) return;
    const event = sim.step();
    if (event) {
      processSimEvent(event);
    }
    updateVisualNodes();
    updateStats();
    setAnimatedTxs(Array.from(txAnimationsRef.current.values()));
    setAnimatedBlocks(Array.from(blockAnimationsRef.current.values()));
  }, [updateVisualNodes, updateStats, processSimEvent]);

  const setSpeed = useCallback((newSpeed: number) => {
    speedRef.current = newSpeed;
    setSpeedState(newSpeed);
  }, []);

  const getSelectedNodeCache = useCallback((nodeIdx: number): CacheTxInfo[] => {
    const sim = simRef.current;
    if (!sim) return [];
    const txIndices = sim.getNodeCacheTxIndices(nodeIdx);
    return txIndices.map(i => {
      const tx = sim.registry.txs[i]!;
      return {
        txIdx: i,
        txId: tx.txId,
        size_B: tx.size_B,
        isAdversarial: tx.isAdversarial,
      };
    });
  }, []);

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
      forceLayoutRef.current.endDrag(_nodeId);
    }
  }, []);

  const getSimRef = useCallback(() => simRef.current, []);

  return {
    isRunning,
    isPaused,
    speed,
    stats,
    simulationDuration,
    nodes,
    edges,
    animatedTxs,
    animatedBlocks,
    blocks,
    endorserBlocks,
    blockFlash,
    eventLog,
    fullEventLog,
    initialize,
    applyConfig,
    start,
    pause,
    resume,
    reset,
    step: stepOnce,
    setSpeed,
    getSelectedNodeCache,
    onDragStart,
    onDrag,
    onDragEnd,
    getSimRef,
    nodeOrder,
    honestCount: honestNodeCount,
  };
}
