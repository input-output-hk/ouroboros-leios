import { useState, useEffect, useCallback } from 'react';
import { type SimulationConfig, type PresetType, DEFAULT_CONFIG, MINIMAL_CONFIG } from '@/simulation';

// Theme colors from Leios site
const COLORS = {
  background: '#200830',
  border: '#45364e',
  text: '#f8f6fa',
  textMuted: '#8f6dae',
  accent: '#6effd1',
  adversary: '#ef4444',
};

// Custom slider styles
const sliderStyles = `
  input[type="range"]::-webkit-slider-thumb {
    -webkit-appearance: none;
    appearance: none;
    width: 16px;
    height: 16px;
    border-radius: 50%;
    background: ${COLORS.accent};
    cursor: pointer;
    border: 2px solid #a7ffe8;
    margin-top: -6px;
    box-shadow: 0 0 8px rgba(110, 255, 209, 0.3);
  }
  input[type="range"]::-moz-range-thumb {
    width: 16px;
    height: 16px;
    border-radius: 50%;
    background: ${COLORS.accent};
    cursor: pointer;
    border: 2px solid #a7ffe8;
    box-shadow: 0 0 8px rgba(110, 255, 209, 0.3);
  }
  input[type="range"]::-webkit-slider-runnable-track {
    height: 4px;
    border-radius: 2px;
    background: ${COLORS.border};
  }
  input[type="range"]::-moz-range-track {
    height: 4px;
    border-radius: 2px;
    background: ${COLORS.border};
  }
`;

const PRESETS: Record<Exclude<PresetType, 'custom'>, SimulationConfig> = {
  minimal: MINIMAL_CONFIG,
  default: DEFAULT_CONFIG,
};

function configsEqual(a: SimulationConfig, b: SimulationConfig): boolean {
  return (
    a.nodes === b.nodes &&
    a.degree === b.degree &&
    a.adversaries === b.adversaries &&
    a.adversaryDegree === b.adversaryDegree &&
    a.adversaryDelay === b.adversaryDelay &&
    a.txCount === b.txCount &&
    a.duration === b.duration &&
    a.blockInterval === b.blockInterval &&
    a.block === b.block &&
    a.latency === b.latency &&
    a.bandwidth === b.bandwidth
  );
}

function detectPreset(config: SimulationConfig): PresetType {
  if (configsEqual(config, MINIMAL_CONFIG)) return 'minimal';
  if (configsEqual(config, DEFAULT_CONFIG)) return 'default';
  return 'custom';
}

interface SliderProps {
  label: string;
  value: number;
  min: number;
  max: number;
  step?: number;
  unit?: string;
  tooltip?: string;
  onChange: (value: number) => void;
}

function Slider({ label, value, min, max, step = 1, unit = '', tooltip, onChange }: SliderProps) {
  return (
    <div className="flex flex-col gap-2" title={tooltip}>
      <div className="flex justify-between items-baseline">
        <span className="text-xs flex items-center gap-1" style={{ color: COLORS.textMuted }}>
          {label}
          {tooltip && (
            <span
              className="inline-flex items-center justify-center w-3.5 h-3.5 rounded-full text-[9px] font-bold cursor-help"
              style={{ backgroundColor: COLORS.textMuted, color: COLORS.background }}
              title={tooltip}
            >
              ?
            </span>
          )}
        </span>
        <span className="text-sm font-mono font-medium" style={{ color: COLORS.text }}>{value}{unit}</span>
      </div>
      <input
        type="range"
        min={min}
        max={max}
        step={step}
        value={value}
        onChange={(e) => onChange(Number(e.target.value))}
        className="w-full appearance-none cursor-pointer bg-transparent"
      />
    </div>
  );
}

interface SectionProps {
  title: string;
  titleColor?: string;
  defaultOpen?: boolean;
  children: React.ReactNode;
}

function Section({ title, titleColor, defaultOpen = true, children }: SectionProps) {
  const [isOpen, setIsOpen] = useState(defaultOpen);

  return (
    <div className="pt-4" style={{ borderTop: `1px solid ${COLORS.border}` }}>
      <button
        onClick={() => setIsOpen(!isOpen)}
        className="flex items-center justify-between text-sm font-medium mb-3 hover:opacity-80 transition-opacity w-full text-left cursor-pointer"
        style={{ color: titleColor || COLORS.text }}
      >
        <span>{title}</span>
        <svg
          className={`w-4 h-4 transition-transform ${isOpen ? 'rotate-180' : ''}`}
          fill="none"
          stroke="currentColor"
          strokeWidth={2}
          viewBox="0 0 24 24"
        >
          <path strokeLinecap="round" strokeLinejoin="round" d="M19 9l-7 7-7-7" />
        </svg>
      </button>
      {isOpen && <div className="space-y-4">{children}</div>}
    </div>
  );
}

interface PresetTabProps {
  preset: PresetType;
  activePreset: PresetType;
  onClick: () => void;
  label: string;
}

function PresetTab({ preset, activePreset, onClick, label }: PresetTabProps) {
  const isActive = preset === activePreset;
  return (
    <button
      onClick={onClick}
      className="flex-1 py-1.5 text-xs font-medium rounded transition-all cursor-pointer"
      style={{
        backgroundColor: isActive ? COLORS.accent : 'transparent',
        color: isActive ? COLORS.background : COLORS.textMuted,
      }}
    >
      {label}
    </button>
  );
}

interface ControlsProps {
  onConfigChange: (config: SimulationConfig) => void;
  disabled?: boolean;
  isExpanded: boolean;
  onToggleExpand: () => void;
}

export function Controls({ onConfigChange, disabled = false, isExpanded, onToggleExpand }: ControlsProps) {
  const [config, setConfig] = useState<SimulationConfig>({ ...MINIMAL_CONFIG });
  const [activePreset, setActivePreset] = useState<PresetType>('minimal');

  // Only call onConfigChange when config changes, not when the callback reference changes
  // eslint-disable-next-line react-hooks/exhaustive-deps
  useEffect(() => {
    onConfigChange(config);
  }, [config]);

  const handlePresetChange = useCallback((preset: Exclude<PresetType, 'custom'>) => {
    setConfig({ ...PRESETS[preset] });
    setActivePreset(preset);
  }, []);

  useEffect(() => {
    setConfig(prev => {
      let changed = false;
      const next = { ...prev };

      if (next.degree >= next.nodes) {
        next.degree = Math.max(1, next.nodes - 1);
        changed = true;
      }

      if (next.adversaryDegree > next.nodes) {
        next.adversaryDegree = next.nodes;
        changed = true;
      }

      return changed ? next : prev;
    });
  }, [config.nodes]);

  const updateConfig = <K extends keyof SimulationConfig>(key: K, value: SimulationConfig[K]) => {
    setConfig(prev => {
      const next = { ...prev, [key]: value };

      if (key === 'block') {
        next.mempool = (value as number) * 2;
      }

      if (next.degree >= next.nodes) {
        next.degree = Math.max(1, next.nodes - 1);
      }

      if (next.adversaryDegree > next.nodes) {
        next.adversaryDegree = next.nodes;
      }

      // Detect if we've left a preset
      setActivePreset(detectPreset(next));

      return next;
    });
  };

  const maxDegree = Math.min(10, config.nodes - 1);
  const maxAdversaryDegree = Math.min(50, config.nodes);

  return (
    <div
      className={`p-4 rounded-lg ${disabled ? 'opacity-50 pointer-events-none' : ''}`}
      style={{ backgroundColor: COLORS.background }}
    >
      <style>{sliderStyles}</style>

      {/* Header with collapse toggle */}
      <button
        onClick={onToggleExpand}
        className="flex items-center justify-between w-full text-left cursor-pointer hover:opacity-80 transition-opacity"
      >
        <h2 className="text-sm font-semibold tracking-wide" style={{ color: COLORS.text }}>
          Parameters
        </h2>
        <svg
          className={`w-4 h-4 transition-transform ${isExpanded ? 'rotate-180' : ''}`}
          fill="none"
          stroke={COLORS.textMuted}
          strokeWidth={2}
          viewBox="0 0 24 24"
        >
          <path strokeLinecap="round" strokeLinejoin="round" d="M19 9l-7 7-7-7" />
        </svg>
      </button>

      {isExpanded && (
        <div className="mt-4">
          {/* Preset tabs */}
          <div
            className="flex gap-1 p-1 rounded-lg mb-4"
            style={{ backgroundColor: COLORS.border }}
          >
            <PresetTab
              preset="minimal"
              activePreset={activePreset}
              onClick={() => handlePresetChange('minimal')}
              label="Minimal"
            />
            <PresetTab
              preset="default"
              activePreset={activePreset}
              onClick={() => handlePresetChange('default')}
              label="Default"
            />
            <PresetTab
              preset="custom"
              activePreset={activePreset}
              onClick={() => {}} // Custom is auto-selected
              label="Custom"
            />
          </div>

          <Section title="Network Topology" defaultOpen={true}>
            <Slider
              label="Honest Nodes"
              value={config.nodes}
              min={10}
              max={250}
              tooltip="Number of honest nodes in the network that follow the protocol"
              onChange={(v) => updateConfig('nodes', v)}
            />
            <Slider
              label="Node Degree"
              value={config.degree}
              min={2}
              max={maxDegree}
              tooltip="Number of peers each honest node connects to (network connectivity)"
              onChange={(v) => updateConfig('degree', v)}
            />
          </Section>

          <Section title="Adversary Settings" titleColor={COLORS.adversary} defaultOpen={true}>
            <Slider
              label="Adversary Nodes"
              value={config.adversaries}
              min={0}
              max={50}
              tooltip="Number of adversary nodes that attempt to front-run transactions"
              onChange={(v) => updateConfig('adversaries', v)}
            />
            <Slider
              label="Degree (each direction)"
              value={config.adversaryDegree}
              min={1}
              max={maxAdversaryDegree}
              tooltip="How many honest nodes each adversary connects to (in and out)"
              onChange={(v) => updateConfig('adversaryDegree', v)}
            />
            <Slider
              label="Front-run delay"
              value={Math.round(config.adversaryDelay * 1000000)}
              min={0}
              max={5000}
              step={250}
              unit="μs"
              tooltip="How many microseconds it takes the adversary to create a front-run transaction"
              onChange={(v) => updateConfig('adversaryDelay', v / 1000000)}
            />
          </Section>

          <Section title="Simulation" defaultOpen={false}>
            <Slider
              label="Duration"
              value={config.duration}
              min={5}
              max={60}
              unit="s"
              tooltip="Total simulation duration - blocks are produced randomly within this window"
              onChange={(v) => updateConfig('duration', v)}
            />
            <Slider
              label="Transaction Count"
              value={config.txCount}
              min={50}
              max={500}
              step={10}
              tooltip="Total number of honest transactions to inject into the network"
              onChange={(v) => updateConfig('txCount', v)}
            />
          </Section>

          <Section title="Block Production" defaultOpen={false}>
            <Slider
              label="Avg Block Interval"
              value={config.blockInterval}
              min={1}
              max={10}
              step={0.5}
              unit="s"
              tooltip="Average time between blocks (Poisson process) - actual timing is random"
              onChange={(v) => updateConfig('blockInterval', v)}
            />
            <Slider
              label="Block Size"
              value={Math.round(config.block / 1000)}
              min={10}
              max={200}
              unit="KB"
              tooltip="Maximum size of each block (affects how many txs fit)"
              onChange={(v) => updateConfig('block', v * 1000)}
            />
          </Section>

          <Section title="Network Properties" defaultOpen={false}>
            <Slider
              label="Latency"
              value={Math.round(config.latency * 1000)}
              min={10}
              max={500}
              step={10}
              unit="ms"
              tooltip="Network delay between nodes (propagation time)"
              onChange={(v) => updateConfig('latency', v / 1000)}
            />
            <Slider
              label="Bandwidth"
              value={Math.round(config.bandwidth * 8 / 1000000)}
              min={1}
              max={100}
              unit=" Mbps"
              tooltip="Network throughput capacity between nodes"
              onChange={(v) => updateConfig('bandwidth', v * 1000000 / 8)}
            />
          </Section>
        </div>
      )}
    </div>
  );
}
