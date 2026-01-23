import { useCallback, useEffect, useState, useRef } from 'react';
import { Controls } from '@/components/Controls';
import { Canvas, type SelectedNodeInfo } from '@/components/Canvas';
import { Statistics } from '@/components/Statistics';
import { Timeline } from '@/components/Timeline';
import { PeerInfo } from '@/components/PeerInfo';
import { EventLog } from '@/components/EventLog';
import { useSimulation } from '@/hooks/useSimulation';
import { COLORS } from '@/theme';
import type { SimulationConfig, LayoutType, P2PConfig } from '@/simulation';
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
  const [currentConfig, setCurrentConfig] = useState<SimulationConfig | null>(null);
  const autoPlayTriggered = useRef(false);
  const {
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
    step,
    setSpeed,
    setP2PConfig,
    onDragStart,
    onDrag,
    onDragEnd,
  } = useSimulation(layoutType);

  const handleConfigChange = useCallback((config: SimulationConfig) => {
    // Config changes regenerate topology (only when not actively running)
    if (!isRunning) {
      setSelectedNode(null);
      setCurrentConfig(config);
      initialize(config);
      if (!isInitialized) {
        setTimeout(() => setIsInitialized(true), 300);
      }
    }
  }, [isRunning, initialize, isInitialized]);

  const handleP2PConfigChange = useCallback((config: P2PConfig) => {
    setP2PConfig(config);
    // Reinitialize simulation with new P2P config (if we have a config and not running)
    if (currentConfig && !isRunning) {
      setSelectedNode(null);
      // Small delay to ensure P2P config ref is updated before initialize runs
      setTimeout(() => initialize(currentConfig), 0);
    }
  }, [setP2PConfig, currentConfig, isRunning, initialize]);

  const handleReset = useCallback(() => {
    setSelectedNode(null);
    reset();
  }, [reset]);

  const handleSelectPeer = useCallback((peerId: string) => {
    const peerNode = nodes.find(n => n.id === peerId);
    if (peerNode) {
      const upstream = edges.filter(e => e.target === peerId).map(e => e.source);
      const downstream = edges.filter(e => e.source === peerId).map(e => e.target);
      setSelectedNode({
        id: peerId,
        honest: peerNode.honest,
        upstream,
        downstream,
      });
    }
  }, [nodes, edges]);

  // Update selected node's upstream/downstream when edges change (for P2P churn)
  useEffect(() => {
    if (selectedNode) {
      const upstream = edges.filter(e => e.target === selectedNode.id).map(e => e.source);
      const downstream = edges.filter(e => e.source === selectedNode.id).map(e => e.target);
      // Only update if peers actually changed
      const upstreamChanged = upstream.length !== selectedNode.upstream.length ||
        upstream.some(p => !selectedNode.upstream.includes(p));
      const downstreamChanged = downstream.length !== selectedNode.downstream.length ||
        downstream.some(p => !selectedNode.downstream.includes(p));
      if (upstreamChanged || downstreamChanged) {
        setSelectedNode(prev => prev ? { ...prev, upstream, downstream } : null);
      }
    }
  }, [edges, selectedNode]);

  // Auto-play in embed mode: initialize and start when component becomes visible
  useEffect(() => {
    if (!embedParams.current.autoPlay || autoPlayTriggered.current) return;

    const triggerAutoPlay = () => {
      if (autoPlayTriggered.current) return;
      autoPlayTriggered.current = true;

      // Initialize with minimal config for embed
      initialize(MINIMAL_CONFIG);
      setCurrentConfig(MINIMAL_CONFIG);
      setIsInitialized(true);

      // Set speed if specified
      if (embedParams.current.speed && embedParams.current.speed !== 1) {
        setSpeed(embedParams.current.speed);
      }

      // Start after a brief delay to allow initialization
      setTimeout(() => {
        start();
      }, 500);
    };

    // Use IntersectionObserver to detect when iframe becomes visible
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
      // Fallback: just trigger immediately
      triggerAutoPlay();
    }
  }, [initialize, start, setSpeed]);

  // Loop simulation in embed mode: restart when finished
  useEffect(() => {
    if (!embedParams.current.loop || !embedParams.current.autoPlay) return;
    if (!isInitialized || !simulationDuration) return;

    // Check if simulation has finished (not running and time reached end)
    if (!isRunning && !isPaused && stats.currentTime >= simulationDuration - 0.1) {
      // Reset and restart after a brief pause
      const restartTimer = setTimeout(() => {
        reset();
        setTimeout(() => {
          start();
        }, 300);
      }, 2000); // 2 second pause before restart

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
      {/* Full-screen canvas */}
      <Canvas
        nodes={nodes}
        edges={edges}
        animatedTxs={animatedTxs}
        blockFlash={blockFlash}
        blockCount={blocks.length}
        selectedNode={selectedNode}
        onNodeSelect={setSelectedNode}
        onDragStart={onDragStart}
        onDrag={onDrag}
        onDragEnd={onDragEnd}
        layoutType={layoutType}
        zoom={zoom}
        onZoomChange={setZoom}
      />

      {/* Loading indicator - spinning circle (hide in embed mode) */}
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
          <div className="overflow-y-auto rounded" style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)' }}>
            <Controls
              onConfigChange={handleConfigChange}
              onP2PConfigChange={handleP2PConfigChange}
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
          <div className="rounded" style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)' }}>
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

      {/* Right panel: Peer Info + Statistics + Event Log */}
      {showRightPanel && (
        <div className="absolute top-2 right-2 z-10 w-60 flex flex-col gap-1 max-h-[calc(100vh-1rem)] overflow-y-auto">
          {selectedNode && (
            <div className="rounded" style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)' }}>
              <PeerInfo
                selectedNode={selectedNode}
                onClose={() => setSelectedNode(null)}
                onSelectPeer={handleSelectPeer}
              />
            </div>
          )}
          <div className="rounded" style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)' }}>
            <Statistics stats={stats} blocks={blocks} />
          </div>
          <div className="rounded" style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)' }}>
            <EventLog entries={eventLog} fullLog={fullEventLog} />
          </div>
        </div>
      )}

      {/* Legend - bottom left */}
      {showLegendPanel && (
        <div
          className="absolute bottom-2 left-2 z-10 p-2 rounded text-xs"
          style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)', color: COLORS.text }}
        >
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
          <div className="flex items-center gap-2">
            <div className="w-3 h-3 rounded-full border-2" style={{ borderColor: COLORS.frontrun, backgroundColor: 'transparent' }} />
            <span>Poisoned Mempool</span>
          </div>
        </div>
      )}

      {/* Zoom and Layout controls - bottom right */}
      {showZoomPanel && (
        <div
          className="absolute bottom-2 right-2 z-10 p-2 rounded flex items-center gap-2"
          style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)' }}
        >
          <button
            onClick={() => setLayoutType(layoutType === 'circular' ? 'force' : 'circular')}
            disabled={isRunning}
            className="px-2 h-6 rounded text-xs cursor-pointer hover:opacity-80 disabled:opacity-40 disabled:cursor-not-allowed"
            style={{ backgroundColor: 'rgba(143, 109, 174, 0.3)', color: COLORS.textMuted }}
            title={layoutType === 'circular' ? 'Switch to force layout' : 'Switch to circular layout'}
          >
            {layoutType === 'circular' ? '○ Circular' : '◉ Force'}
          </button>
          <div className="flex items-center gap-1">
            <button
              onClick={() => setZoom(Math.max(0.5, zoom - 0.25))}
              className="w-6 h-6 rounded flex items-center justify-center text-xs font-bold cursor-pointer hover:opacity-80"
              style={{ backgroundColor: 'rgba(143, 109, 174, 0.3)', color: COLORS.textMuted }}
              title="Zoom out"
            >
              −
            </button>
            <span
              className="text-xs font-mono px-1"
              style={{ color: COLORS.textMuted, minWidth: '36px', textAlign: 'center' }}
            >
              {Math.round(zoom * 100)}%
            </span>
            <button
              onClick={() => setZoom(Math.min(3, zoom + 0.25))}
              className="w-6 h-6 rounded flex items-center justify-center text-xs font-bold cursor-pointer hover:opacity-80"
              style={{ backgroundColor: 'rgba(143, 109, 174, 0.3)', color: COLORS.textMuted }}
              title="Zoom in"
            >
              +
            </button>
          </div>
        </div>
      )}
    </div>
  );
}
