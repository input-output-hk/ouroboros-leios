import { useCallback, useEffect, useState, useRef } from 'react';
import { Controls } from '@/components/Controls';
import { Canvas, type SelectedNodeInfo } from '@/components/Canvas';
import { MatrixCanvas, ZOOM_LEVELS } from '@/components/MatrixCanvas';
import { Statistics } from '@/components/Statistics';
import { Timeline } from '@/components/Timeline';
import { PeerInfo } from '@/components/PeerInfo';
import { EventLog } from '@/components/EventLog';
import { TxCache } from '@/components/TxCache';
import { useSimulation } from '@/hooks/useSimulation';
import { COLORS } from '@/theme';
import type { SimulationConfig, LayoutType } from '@/simulation';
import { MINIMAL_CONFIG } from '@/simulation';

// Parse URL parameters for embed mode
function getEmbedParams() {
  const params = new URLSearchParams(window.location.search);
  return {
    embed: params.get('embed') === 'true',
    autoPlay: params.get('autoPlay') === 'true',
    loop: params.get('loop') === 'true',
    hideControls: params.get('hideControls') === 'true',
    hideStats: params.get('hideStats') === 'true',
    hideTimeline: params.get('hideTimeline') === 'true',
    hideLegend: params.get('hideLegend') === 'true',
    hideZoom: params.get('hideZoom') === 'true',
    speed: parseFloat(params.get('speed') || '1'),
  };
}

export default function App() {
  const embedParams = useRef(getEmbedParams());
  const isEmbedMode = embedParams.current.embed;

  const [selectedNode, setSelectedNode] = useState<SelectedNodeInfo | null>(null);
  const [showControls, setShowControls] = useState(!isEmbedMode && !embedParams.current.hideControls);
  const [layoutType, setLayoutType] = useState<LayoutType>('circular');
  const [isInitialized, setIsInitialized] = useState(false);
  const [zoom, setZoom] = useState(1);
  const [matrixZoomIdx, setMatrixZoomIdx] = useState(0);
  const [currentConfig, setCurrentConfig] = useState<SimulationConfig | null>(null);
  const fitViewFnRef = useRef<(() => void) | null>(null);
  const autoPlayTriggered = useRef(false);
  const [windowSize, setWindowSize] = useState({ w: window.innerWidth, h: window.innerHeight });
  const {
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
    blockFlash,
    endorserBlocks,
    eventLog,
    fullEventLog,
    initialize,
    applyConfig,
    start,
    pause,
    resume,
    reset,
    step,
    setSpeed,
    getSelectedNodeCache,
    onDragStart,
    onDrag,
    onDragEnd,
    getSimRef,
    nodeOrder,
    honestCount,
  } = useSimulation(layoutType);

  const ebEnabled = currentConfig?.ebEnabled ?? false;

  // Keys that affect network topology — changes to these require full initialize()
  const TOPOLOGY_KEYS: (keyof SimulationConfig)[] = [
    'nodes', 'degree', 'adversaries', 'adversaryDegree', 'adversaryDelay',
    'mempool', 'latency', 'bandwidth',
  ];

  const handleConfigChange = useCallback((config: SimulationConfig) => {
    if (!isRunning) {
      setSelectedNode(null);

      // Auto-switch layout based on node count
      const totalNodes = config.nodes + config.adversaries;
      if (totalNodes > 200 && layoutType !== 'matrix') {
        setLayoutType('matrix');
      } else if (totalNodes <= 200 && layoutType === 'matrix') {
        setLayoutType('circular');
      }

      const topologyChanged = !currentConfig ||
        TOPOLOGY_KEYS.some(k => config[k] !== currentConfig[k]);

      if (topologyChanged) {
        initialize(config);
      } else {
        applyConfig(config);
      }

      setCurrentConfig(config);
      if (!isInitialized) {
        setTimeout(() => setIsInitialized(true), 300);
      }
    }
  }, [isRunning, initialize, applyConfig, isInitialized, layoutType, currentConfig]);

  const handleReset = useCallback(() => {
    setSelectedNode(null);
    reset();
  }, [reset]);

  const handleSelectPeer = useCallback((peerId: string) => {
    // In matrix mode, use sim directly for peer info
    const sim = getSimRef();
    if (sim) {
      const lightNode = sim.nodes.find(n => n.id === peerId);
      if (lightNode) {
        const upstream = lightNode.upstreamPeers.map(i => sim.nodes[i]?.id ?? `#${i}`);
        const downstream = lightNode.downstreamPeers.map(i => sim.nodes[i]?.id ?? `#${i}`);
        setSelectedNode({
          id: peerId,
          idx: lightNode.idx,
          honest: lightNode.honest,
          upstream,
          downstream,
        });
        return;
      }
    }

    // Fallback: use visual nodes
    const peerNode = nodes.find(n => n.id === peerId);
    if (peerNode) {
      const upstream = edges.filter(e => e.target === peerId).map(e => e.source);
      const downstream = edges.filter(e => e.source === peerId).map(e => e.target);
      const idx = parseInt(peerId.slice(1)) - (peerId.startsWith('H') ? 1 : 0);
      setSelectedNode({
        id: peerId,
        idx,
        honest: peerNode.honest,
        upstream,
        downstream,
      });
    }
  }, [nodes, edges, getSimRef]);

  // Update selected node's upstream/downstream when edges change
  useEffect(() => {
    if (selectedNode) {
      const upstream = edges.filter(e => e.target === selectedNode.id).map(e => e.source);
      const downstream = edges.filter(e => e.source === selectedNode.id).map(e => e.target);
      const upstreamChanged = upstream.length !== selectedNode.upstream.length ||
        upstream.some(p => !selectedNode.upstream.includes(p));
      const downstreamChanged = downstream.length !== selectedNode.downstream.length ||
        downstream.some(p => !selectedNode.downstream.includes(p));
      if (upstreamChanged || downstreamChanged) {
        setSelectedNode(prev => prev ? { ...prev, upstream, downstream } : null);
      }
    }
  }, [edges, selectedNode]);

  // Handle node selection from canvas — need to add idx
  const handleNodeSelect = useCallback((info: SelectedNodeInfo | null) => {
    if (info) {
      // Find the LightNode index from the nodes array
      const node = nodes.find(n => n.id === info.id);
      if (node) {
        // node index is encoded in the id: H1 = idx 0, H2 = idx 1, etc.
        // But with adversary nodes it's trickier. We need the actual LightNode.idx.
        // For now, find it by looking up the position in the nodes array
        const nodeIdx = nodes.indexOf(node);
        setSelectedNode({ ...info, idx: nodeIdx });
      }
    } else {
      setSelectedNode(null);
    }
  }, [nodes]);

  // Handle node selection from matrix canvas
  const handleMatrixNodeSelect = useCallback((nodeIdx: number | null) => {
    if (nodeIdx === null) {
      setSelectedNode(null);
      return;
    }
    const sim = getSimRef();
    if (!sim) return;
    const node = sim.nodes[nodeIdx];
    if (!node) return;
    const upstream = node.upstreamPeers.map(i => sim.nodes[i]?.id ?? `#${i}`);
    const downstream = node.downstreamPeers.map(i => sim.nodes[i]?.id ?? `#${i}`);
    setSelectedNode({
      id: node.id,
      idx: nodeIdx,
      honest: node.honest,
      upstream,
      downstream,
    });
  }, [getSimRef]);

  // Track window size for matrix canvas
  useEffect(() => {
    const handleResize = () => setWindowSize({ w: window.innerWidth, h: window.innerHeight });
    window.addEventListener('resize', handleResize);
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  // Auto-play in embed mode
  useEffect(() => {
    if (!embedParams.current.autoPlay || autoPlayTriggered.current) return;

    const triggerAutoPlay = () => {
      if (autoPlayTriggered.current) return;
      autoPlayTriggered.current = true;

      initialize(MINIMAL_CONFIG);
      setCurrentConfig(MINIMAL_CONFIG);
      setIsInitialized(true);

      if (embedParams.current.speed && embedParams.current.speed !== 1) {
        setSpeed(embedParams.current.speed);
      }

      setTimeout(() => {
        start();
      }, 500);
    };

    if ('IntersectionObserver' in window) {
      const observer = new IntersectionObserver(
        (entries) => {
          if (entries[0].isIntersecting) {
            triggerAutoPlay();
            observer.disconnect();
          }
        },
        { threshold: 0.1 }
      );
      observer.observe(document.body);
      return () => observer.disconnect();
    } else {
      triggerAutoPlay();
    }
  }, [initialize, start, setSpeed]);

  // Loop simulation in embed mode
  useEffect(() => {
    if (!embedParams.current.loop || !embedParams.current.autoPlay) return;
    if (!isInitialized || !simulationDuration) return;

    if (!isRunning && !isPaused && stats.currentTime >= simulationDuration - 0.1) {
      const restartTimer = setTimeout(() => {
        reset();
        setTimeout(() => {
          start();
        }, 300);
      }, 2000);

      return () => clearTimeout(restartTimer);
    }
  }, [isRunning, isPaused, stats.currentTime, simulationDuration, isInitialized, reset, start]);

  // Determine which panels to show
  const showLeftPanel = !isEmbedMode && !embedParams.current.hideControls;
  const showRightPanel = !isEmbedMode && !embedParams.current.hideStats;
  const showTimelinePanel = !isEmbedMode && !embedParams.current.hideTimeline;
  const showLegendPanel = !isEmbedMode && !embedParams.current.hideLegend;
  const showZoomPanel = !isEmbedMode && !embedParams.current.hideZoom;

  return (
    <div className="h-screen w-screen overflow-hidden relative" style={{ backgroundColor: COLORS.background }}>
      {/* Full-screen canvas — matrix or graph */}
      {layoutType === 'matrix' ? (
        <MatrixCanvas
          sim={getSimRef()}
          nodeOrder={nodeOrder}
          honestCount={honestCount}
          blockFlash={blockFlash}
          selectedNodeIdx={selectedNode?.idx ?? null}
          onNodeSelect={handleMatrixNodeSelect}
          width={windowSize.w}
          height={windowSize.h}
          zoomIdx={matrixZoomIdx}
          onZoomIdxChange={setMatrixZoomIdx}
          onRegisterFitView={(fn) => { fitViewFnRef.current = fn; }}
        />
      ) : (
        <Canvas
          nodes={nodes}
          edges={edges}
          animatedTxs={animatedTxs}
          animatedBlocks={animatedBlocks}
          blockFlash={blockFlash}
          blockCount={blocks.length}
          selectedNode={selectedNode}
          onNodeSelect={handleNodeSelect}
          onDragStart={onDragStart}
          onDrag={onDrag}
          onDragEnd={onDragEnd}
          layoutType={layoutType}
          zoom={zoom}
          onZoomChange={setZoom}
          onRegisterFitView={(fn) => { fitViewFnRef.current = fn; }}
        />
      )}

      {/* Loading indicator */}
      {!isInitialized && !isEmbedMode && (
        <div className="absolute inset-0 flex items-center justify-center z-20">
          <div className="flex flex-col items-center gap-4">
            <svg width="48" height="48" viewBox="0 0 48 48" className="animate-spin">
              <circle
                cx="24" cy="24" r="20"
                fill="none"
                stroke={COLORS.accent}
                strokeWidth="4"
                strokeLinecap="round"
                strokeDasharray="90 150"
                opacity="0.9"
              />
            </svg>
          </div>
        </div>
      )}

      {/* Left panel: Title + Controls */}
      {showLeftPanel && (
        <div className="absolute top-2 left-2 z-10 w-60 flex flex-col gap-1 max-h-[calc(100vh-1rem)]">
          <div className="px-4 py-2 flex items-center gap-2">
            <a
              href="https://leios.cardano-scaling.org/"
              className="hover:opacity-70 transition-opacity"
              style={{ color: COLORS.textMuted }}
              title="Back to Leios site"
            >
              <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
                <polyline points="15 18 9 12 15 6" />
              </svg>
            </a>
            <h1 className="text-lg font-bold" style={{ color: COLORS.text }}>
              Mempool Simulation
            </h1>
          </div>
          <div className="overflow-y-auto rounded backdrop-blur-md" style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)' }}>
            <Controls
              onConfigChange={handleConfigChange}
              disabled={isRunning}
              isExpanded={showControls}
              onToggleExpand={() => setShowControls(!showControls)}
            />
          </div>
        </div>
      )}

      {/* Bottom center: Timeline controls */}
      {showTimelinePanel && (
        <div className="absolute bottom-4 left-1/2 -translate-x-1/2 z-10">
          <div className="rounded backdrop-blur-md" style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)' }}>
            <Timeline
              isRunning={isRunning}
              isPaused={isPaused}
              speed={speed}
              currentTime={stats.currentTime}
              totalDuration={simulationDuration}
              onStart={start}
              onPause={pause}
              onResume={resume}
              onReset={handleReset}
              onStep={step}
              onSpeedChange={setSpeed}
            />
          </div>
        </div>
      )}

      {/* Right panel: Peer Info + TxCache + Statistics + Event Log */}
      {showRightPanel && (
        <div className="absolute top-2 right-2 z-10 w-60 flex flex-col gap-1 max-h-[calc(100vh-1rem)] overflow-y-auto">
          {selectedNode && (
            <div className="rounded backdrop-blur-md" style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)' }}>
              <PeerInfo
                selectedNode={selectedNode}
                onClose={() => setSelectedNode(null)}
                onSelectPeer={handleSelectPeer}
              />
            </div>
          )}
          {selectedNode && ebEnabled && (
            <div className="rounded backdrop-blur-md" style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)' }}>
              <TxCache
                nodeIdx={selectedNode.idx}
                getCache={getSelectedNodeCache}
              />
            </div>
          )}
          <div className="rounded backdrop-blur-md" style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)' }}>
            <Statistics stats={stats} blocks={blocks} ebEnabled={ebEnabled} endorserBlocks={endorserBlocks} />
          </div>
          <div className="rounded backdrop-blur-md" style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)' }}>
            <EventLog entries={eventLog} fullLog={fullEventLog} />
          </div>
        </div>
      )}

      {/* Legend - bottom left */}
      {showLegendPanel && (
        <div
          className="absolute bottom-2 left-2 z-10 p-2 rounded backdrop-blur-md text-xs"
          style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)', color: COLORS.text }}
        >
          {layoutType === 'matrix' ? (
            <>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3" style={{ backgroundColor: '#6effd1' }} />
                <span>Node → Peer (downstream)</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3" style={{ backgroundColor: '#fbbf24' }} />
                <span>Node ← Peer (upstream)</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3" style={{ backgroundColor: '#e85df5' }} />
                <span>Node ↔ Peer (both)</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3" style={{ background: 'linear-gradient(135deg, #6effd1, #0a2015)' }} />
                <span>Diagonal = mempool fill</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3" style={{ backgroundColor: '#ef4444' }} />
                <span>Poisoned / adversary sep</span>
              </div>
            </>
          ) : (
            <>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3 rounded-full" style={{ backgroundColor: COLORS.accent }} />
                <span>Honest Node</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3 rounded-full" style={{ backgroundColor: COLORS.adversary }} />
                <span>Adversary Node</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-2 h-2 rounded-full" style={{ backgroundColor: COLORS.accent }} />
                <span>Honest Tx</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-2 h-2 rounded-full" style={{ backgroundColor: COLORS.frontrun }} />
                <span>Front-run Tx</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3 rounded-full border-2" style={{ borderColor: COLORS.frontrun, backgroundColor: 'transparent' }} />
                <span>Poisoned Mempool</span>
              </div>
              <div className="flex items-center gap-2 mb-1">
                <div className="w-3 h-3" style={{ backgroundColor: '#fbbf24' }} />
                <span>Block (RB)</span>
              </div>
              <div className="flex items-center gap-2">
                <div className="w-3 h-3 rotate-45" style={{ backgroundColor: '#22d3ee' }} />
                <span>Endorser Block (EB)</span>
              </div>
            </>
          )}
        </div>
      )}

      {/* Zoom and Layout controls - bottom right */}
      {showZoomPanel && (
        <div
          className="absolute bottom-2 right-2 z-10 p-2 rounded backdrop-blur-md flex items-center gap-2"
          style={{ backgroundColor: 'rgba(32, 8, 48, 0.75)' }}
        >
          <button
            onClick={() => {
              const next = layoutType === 'circular' ? 'force' : layoutType === 'force' ? 'matrix' : 'circular';
              setLayoutType(next);
            }}
            disabled={isRunning}
            className="px-2 h-6 rounded text-xs cursor-pointer hover:opacity-80 disabled:opacity-40 disabled:cursor-not-allowed"
            style={{ backgroundColor: 'rgba(143, 109, 174, 0.3)', color: COLORS.textMuted }}
            title={`Current: ${layoutType}. Click to cycle.`}
          >
            {layoutType === 'circular' ? '○ Circular' : layoutType === 'force' ? '◉ Force' : '▦ Matrix'}
          </button>
          <div className="flex items-center gap-1">
            <button
              onClick={() => {
                if (layoutType === 'matrix') {
                  setMatrixZoomIdx(Math.max(0, matrixZoomIdx - 1));
                } else {
                  setZoom(Math.max(0.5, zoom - 0.25));
                }
              }}
              disabled={layoutType === 'matrix' ? matrixZoomIdx <= 0 : false}
              className="w-6 h-6 rounded flex items-center justify-center text-xs font-bold cursor-pointer hover:opacity-80 disabled:opacity-30 disabled:cursor-not-allowed"
              style={{ backgroundColor: 'rgba(143, 109, 174, 0.3)', color: COLORS.textMuted }}
              title="Zoom out"
            >
              −
            </button>
            <span
              className="text-xs font-mono px-1"
              style={{ color: COLORS.textMuted, minWidth: '36px', textAlign: 'center' }}
            >
              {layoutType === 'matrix'
                ? `${ZOOM_LEVELS[matrixZoomIdx]}×${ZOOM_LEVELS[matrixZoomIdx]}`
                : `${Math.round(zoom * 100)}%`}
            </span>
            <button
              onClick={() => {
                if (layoutType === 'matrix') {
                  setMatrixZoomIdx(Math.min(ZOOM_LEVELS.length - 1, matrixZoomIdx + 1));
                } else {
                  setZoom(Math.min(3, zoom + 0.25));
                }
              }}
              disabled={layoutType === 'matrix' ? matrixZoomIdx >= ZOOM_LEVELS.length - 1 : false}
              className="w-6 h-6 rounded flex items-center justify-center text-xs font-bold cursor-pointer hover:opacity-80 disabled:opacity-30 disabled:cursor-not-allowed"
              style={{ backgroundColor: 'rgba(143, 109, 174, 0.3)', color: COLORS.textMuted }}
              title="Zoom in"
            >
              +
            </button>
          </div>
          <button
            onClick={() => fitViewFnRef.current?.()}
            className="px-2 h-6 rounded text-xs cursor-pointer hover:opacity-80"
            style={{ backgroundColor: 'rgba(143, 109, 174, 0.3)', color: COLORS.textMuted }}
            title="Fit topology to screen"
          >
            Fit
          </button>
        </div>
      )}
    </div>
  );
}
