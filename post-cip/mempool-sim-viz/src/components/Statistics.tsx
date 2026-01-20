import { useRef, useEffect } from 'react';
import type { SimulationStats, Block } from '@/simulation';

// Theme colors from Leios site
const COLORS = {
  background: '#200830',
  backgroundDark: '#180425',
  border: '#45364e',
  text: '#f8f6fa',
  textMuted: '#8f6dae',
  honest: '#6effd1',
  adversary: '#ef4444',
};

interface StatCardProps {
  label: string;
  value: string | number;
  color?: string;
}

function StatCard({ label, value, color }: StatCardProps) {
  return (
    <div className="rounded p-1.5 flex flex-col justify-between h-full" style={{ backgroundColor: COLORS.backgroundDark }}>
      <div className="text-xs" style={{ color: COLORS.textMuted }}>{label}</div>
      <div className="text-sm font-bold font-mono" style={{ color: color || COLORS.text }}>{value}</div>
    </div>
  );
}

interface StatisticsProps {
  stats: SimulationStats;
  blocks: Block[];
}

export function Statistics({ stats, blocks }: StatisticsProps) {
  const frontRunPercent = (stats.frontRunRate * 100).toFixed(1);
  const fillPercent = stats.avgBlockFillPercent.toFixed(1);
  const traceRef = useRef<HTMLDivElement>(null);

  // Auto-scroll to bottom when new blocks are added
  useEffect(() => {
    if (traceRef.current) {
      traceRef.current.scrollTop = traceRef.current.scrollHeight;
    }
  }, [blocks.length]);

  return (
    <div className="p-3 rounded-lg" style={{ backgroundColor: COLORS.background }}>
      <h2 className="text-sm font-semibold mb-3" style={{ color: COLORS.text }}>Statistics</h2>

      <div className="grid grid-cols-2 gap-2 mb-3">
        <StatCard
          label="Time"
          value={`${stats.currentTime.toFixed(1)}s`}
        />
        <StatCard
          label="Events"
          value={stats.eventsProcessed.toLocaleString()}
        />
        <StatCard
          label="Blocks"
          value={stats.blocksProduced}
        />
        <StatCard
          label="Block Fill"
          value={`${fillPercent}%`}
        />
      </div>

      <div className="pt-3 mb-3" style={{ borderTop: `1px solid ${COLORS.border}` }}>
        <div className="grid grid-cols-2 gap-2">
          <StatCard
            label="Honest in Blocks"
            value={stats.totalHonestInBlocks}
            color={COLORS.honest}
          />
          <StatCard
            label="Front-run"
            value={stats.totalAdversarialInBlocks}
            color={COLORS.adversary}
          />
        </div>
      </div>

      <div className="pt-3" style={{ borderTop: `1px solid ${COLORS.border}` }}>
        <div className="text-xs mb-2" style={{ color: COLORS.textMuted }}>Front-run Rate</div>
        <div className="relative h-5 rounded overflow-hidden" style={{ backgroundColor: COLORS.border }}>
          <div
            className="absolute inset-y-0 left-0 transition-all duration-300"
            style={{ width: `${stats.frontRunRate * 100}%`, backgroundColor: 'rgba(239, 68, 68, 0.7)' }}
          />
          <div
            className="absolute inset-y-0 transition-all duration-300"
            style={{
              left: `${stats.frontRunRate * 100}%`,
              right: 0,
              backgroundColor: 'rgba(110, 255, 209, 0.5)',
            }}
          />
          <div className="absolute inset-0 flex items-center justify-center text-xs font-mono" style={{ color: COLORS.text }}>
            {frontRunPercent}%
          </div>
        </div>
      </div>

      {/* Block trace */}
      <div className="pt-3 mt-3" style={{ borderTop: `1px solid ${COLORS.border}` }}>
        <div className="text-xs mb-2" style={{ color: COLORS.textMuted }}>Block Trace</div>
        <div
          ref={traceRef}
          className="max-h-40 overflow-y-auto space-y-1 font-mono text-[11px]"
          style={{ backgroundColor: COLORS.backgroundDark, borderRadius: '4px', padding: '6px' }}
        >
          {blocks.length === 0 ? (
            <div style={{ color: COLORS.border }}>No blocks yet...</div>
          ) : (
            blocks.map((block, index) => (
              <div
                key={block.blockId}
                className="flex items-center gap-2"
              >
                <span style={{ color: COLORS.border, minWidth: '20px' }}>{index + 1}.</span>
                <span style={{ color: COLORS.textMuted }}>{block.timestamp.toFixed(1)}s</span>
                <span style={{ color: COLORS.text }}>{block.producer}</span>
                <span style={{ color: COLORS.border }}>→</span>
                <span>
                  <span style={{ color: COLORS.honest }}>{block.honestCount}</span>
                  <span style={{ color: COLORS.border }}>/</span>
                  <span style={{ color: COLORS.adversary }}>{block.adversarialCount}</span>
                </span>
                <span style={{ color: COLORS.border }}>txs</span>
              </div>
            ))
          )}
        </div>
      </div>
    </div>
  );
}
