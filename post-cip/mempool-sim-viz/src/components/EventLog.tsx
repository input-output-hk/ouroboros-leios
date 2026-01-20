import { useEffect, useRef, useState, useCallback } from 'react';
import type { LogEntry } from '@/hooks/useSimulation';

// Theme colors from Leios site
const COLORS = {
  background: '#200830',
  text: '#f8f6fa',
  textMuted: '#8f6dae',
  honest: '#6effd1',
  adversary: '#ef4444',
  frontrun: '#f97316',
  block: '#fbbf24',
};

interface EventLogProps {
  entries: LogEntry[];
  fullLog: LogEntry[];
  maxHeight?: number;
}

export function EventLog({ entries, fullLog, maxHeight = 200 }: EventLogProps) {
  const scrollRef = useRef<HTMLDivElement>(null);
  const autoScrollRef = useRef(true);
  const [copied, setCopied] = useState(false);

  // Auto-scroll to bottom when new entries arrive, unless user has scrolled up
  useEffect(() => {
    const container = scrollRef.current;
    if (container && autoScrollRef.current) {
      container.scrollTop = container.scrollHeight;
    }
  }, [entries]);

  const handleScroll = () => {
    const container = scrollRef.current;
    if (container) {
      // If user is near the bottom, enable auto-scroll
      const isNearBottom = container.scrollHeight - container.scrollTop - container.clientHeight < 50;
      autoScrollRef.current = isNearBottom;
    }
  };

  const handleCopy = useCallback(() => {
    const text = fullLog.map(entry => {
      const kind = entry.kind === 'submit' ? 'SUB' : entry.kind === 'send' ? 'TX' : entry.kind === 'block' ? 'BLK' : entry.kind.toUpperCase();
      const adv = entry.isAdversarial ? ' [ADV]' : '';
      return `${entry.time.toFixed(2)}s ${kind} ${entry.message}${adv}`;
    }).join('\n');

    navigator.clipboard.writeText(text).then(() => {
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    });
  }, [fullLog]);

  const getKindColor = (kind: string, isAdversarial?: boolean) => {
    if (kind === 'block') return COLORS.block;
    if (isAdversarial) return COLORS.frontrun;
    return COLORS.honest;
  };

  const getKindLabel = (kind: string) => {
    switch (kind) {
      case 'submit': return 'SUB';
      case 'send': return 'TX';
      case 'block': return 'BLK';
      default: return kind.toUpperCase().slice(0, 3);
    }
  };

  return (
    <div className="p-3">
      <div className="flex justify-between items-center mb-2">
        <span className="text-xs font-medium" style={{ color: COLORS.textMuted }}>
          Event Log {fullLog.length > entries.length && `(${entries.length}/${fullLog.length})`}
        </span>
        <button
          onClick={handleCopy}
          className="text-[10px] px-1.5 py-0.5 rounded transition-all hover:scale-105 cursor-pointer"
          style={{ backgroundColor: COLORS.textMuted, color: COLORS.background }}
          title="Copy full log to clipboard"
        >
          {copied ? 'Copied!' : 'Copy'}
        </button>
      </div>
      <div
        ref={scrollRef}
        onScroll={handleScroll}
        className="overflow-y-auto font-mono text-[10px] space-y-0.5"
        style={{ maxHeight, backgroundColor: 'rgba(0,0,0,0.2)', borderRadius: 4, padding: 4 }}
      >
        {entries.length === 0 ? (
          <div style={{ color: COLORS.textMuted }}>No events yet</div>
        ) : (
          entries.map((entry) => (
            <div key={entry.id} className="flex gap-2 leading-tight">
              <span style={{ color: COLORS.textMuted, minWidth: 36 }}>
                {entry.time.toFixed(2)}s
              </span>
              <span
                style={{
                  color: getKindColor(entry.kind, entry.isAdversarial),
                  minWidth: 24,
                  fontWeight: 500,
                }}
              >
                {getKindLabel(entry.kind)}
              </span>
              <span style={{ color: entry.isAdversarial ? COLORS.frontrun : COLORS.text }}>
                {entry.message}
              </span>
            </div>
          ))
        )}
      </div>
    </div>
  );
}
