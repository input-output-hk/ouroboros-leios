import { useCallback, useState } from 'react';
import { Controls } from '@/components/Controls';
import { Canvas, type SelectedNodeInfo } from '@/components/Canvas';
import { Statistics } from '@/components/Statistics';
import { Timeline } from '@/components/Timeline';
import { PeerInfo } from '@/components/PeerInfo';
import { EventLog } from '@/components/EventLog';
import { useSimulation } from '@/hooks/useSimulation';
import { COLORS } from '@/theme';
import type { SimulationConfig, LayoutType } from '@/simulation';

export default function App() {
  const [selectedNode, setSelectedNode] = useState<SelectedNodeInfo | null>(null);
  const [showControls, setShowControls] = useState(true);
  const [layoutType, setLayoutType] = useState<LayoutType>('circular');
  const [isInitialized, setIsInitialized] = useState(false);
  const [zoom, setZoom] = useState(1);
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
    onDragStart,
    onDrag,
    onDragEnd,
  } = useSimulation(layoutType);

  const handleConfigChange = useCallback((config: SimulationConfig) => {
    // Config changes regenerate topology (only when not actively running)
    if (!isRunning) {
      setSelectedNode(null);
      initialize(config);
      if (!isInitialized) {
        setTimeout(() => setIsInitialized(true), 300);
      }
    }
  }, [isRunning, initialize, isInitialized]);

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

      {/* Loading indicator - spinning circle */}
      {!isInitialized && (
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
      <div className="absolute top-2 left-2 z-10 w-60 flex flex-col gap-1 max-h-[calc(100vh-1rem)]">
        <div className="px-4 py-2">
          <h1 className="text-lg font-bold" style={{ color: COLORS.text }}>
            Mempool Simulation
          </h1>
        </div>
        <div className="overflow-y-auto rounded" style={{ backgroundColor: 'rgba(32, 8, 48, 0.9)' }}>
          <Controls
            onConfigChange={handleConfigChange}
            disabled={isRunning}
            isExpanded={showControls}
            onToggleExpand={() => setShowControls(!showControls)}
          />
        </div>
      </div>

      {/* Bottom center: Timeline controls */}
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

      {/* Right panel: Peer Info + Statistics + Event Log */}
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

      {/* Legend - bottom left */}
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

      {/* Zoom and Layout controls - bottom right */}
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
    </div>
  );
}
