import { useRef, useCallback } from 'react';

// Theme colors from Leios site
const COLORS = {
  background: '#200830',
  text: '#f8f6fa',
  textMuted: '#8f6dae',
  accent: '#6effd1',
  warning: '#fbbf24',
};

interface TimelineProps {
  isRunning: boolean;
  isPaused: boolean;
  speed: number;
  currentTime: number;
  totalDuration: number;
  onStart: () => void;
  onPause: () => void;
  onResume: () => void;
  onReset: () => void;
  onStep: () => void;
  onSpeedChange: (speed: number) => void;
}

interface IconButtonProps {
  onClick?: () => void;
  onMouseDown?: () => void;
  onMouseUp?: () => void;
  onMouseLeave?: () => void;
  disabled?: boolean;
  label: string;
  color?: string;
  title?: string;
  children: React.ReactNode;
}

function IconButton({ onClick, onMouseDown, onMouseUp, onMouseLeave, disabled, label, color, title, children }: IconButtonProps) {
  return (
    <button
      onClick={onClick}
      onMouseDown={onMouseDown}
      onMouseUp={onMouseUp}
      onMouseLeave={onMouseLeave}
      disabled={disabled}
      title={title}
      className="flex flex-col items-center gap-1.5 py-3 px-4 transition-all hover:scale-105 active:scale-95 disabled:opacity-40 disabled:cursor-not-allowed disabled:hover:scale-100 cursor-pointer min-w-[60px]"
    >
      <span className="h-8 flex items-center justify-center" style={{ color: color || COLORS.text }}>
        {children}
      </span>
      <span className="text-[10px] uppercase tracking-wider" style={{ color: COLORS.textMuted }}>
        {label}
      </span>
    </button>
  );
}

export function Timeline({
  isRunning,
  isPaused,
  speed,
  currentTime,
  totalDuration,
  onStart,
  onPause,
  onResume,
  onReset,
  onStep,
  onSpeedChange,
}: TimelineProps) {
  const stepIntervalRef = useRef<number | null>(null);

  const startStepping = useCallback(() => {
    onStep();
    stepIntervalRef.current = window.setInterval(() => {
      onStep();
    }, 50);
  }, [onStep]);

  const stopStepping = useCallback(() => {
    if (stepIntervalRef.current) {
      clearInterval(stepIntervalRef.current);
      stepIntervalRef.current = null;
    }
  }, []);

  // Calculate progress percentage
  const progress = totalDuration > 0 ? Math.min(100, (currentTime / totalDuration) * 100) : 0;

  return (
    <div className="rounded-lg overflow-hidden" style={{ backgroundColor: COLORS.background }}>
      <div className="p-4 pb-2 flex items-center justify-between">
        {/* Play/Pause */}
        {!isRunning ? (
          <IconButton onClick={onStart} label="Start" color={COLORS.accent}>
            <svg width="32" height="32" viewBox="0 0 24 24" fill="currentColor">
              <path d="M8 5v14l11-7z" />
            </svg>
          </IconButton>
        ) : isPaused ? (
          <IconButton onClick={onResume} label="Resume" color={COLORS.accent}>
            <svg width="32" height="32" viewBox="0 0 24 24" fill="currentColor">
              <path d="M8 5v14l11-7z" />
            </svg>
          </IconButton>
        ) : (
          <IconButton onClick={onPause} label="Pause" color={COLORS.warning}>
            <svg width="32" height="32" viewBox="0 0 24 24" fill="currentColor">
              <path d="M6 19h4V5H6v14zm8-14v14h4V5h-4z" />
            </svg>
          </IconButton>
        )}

        {/* Step */}
        <IconButton
          onMouseDown={startStepping}
          onMouseUp={stopStepping}
          onMouseLeave={stopStepping}
          disabled={isRunning && !isPaused}
          label="Step"
          title="Hold to step continuously"
        >
          <svg width="32" height="32" viewBox="0 0 24 24" fill="currentColor">
            <path d="M6 18l8.5-6L6 6v12zM16 6v12h2V6h-2z" />
          </svg>
        </IconButton>

        {/* Stop */}
        <IconButton onClick={onReset} label="Stop">
          <svg width="32" height="32" viewBox="0 0 24 24" fill="currentColor">
            <path d="M6 6h12v12H6z" />
          </svg>
        </IconButton>

        {/* Speed - cycles through options on click */}
        <IconButton
          onClick={() => {
            const speeds = [0.5, 1, 2, 5, 10];
            const currentIndex = speeds.indexOf(speed);
            const nextIndex = (currentIndex + 1) % speeds.length;
            onSpeedChange(speeds[nextIndex]!);
          }}
          label="Speed"
        >
          <span className="text-lg font-medium font-mono">{speed}×</span>
        </IconButton>
      </div>

      {/* Progress text - centered above bar */}
      <div className="text-center pb-1.5">
        <span
          className="text-xs font-mono"
          style={{ color: COLORS.textMuted }}
        >
          {Math.min(currentTime, totalDuration).toFixed(1)}s / {totalDuration}s
        </span>
      </div>

      {/* Progress bar - full width at bottom edge */}
      <div
        className="h-1.5"
        style={{ backgroundColor: COLORS.textMuted + '40' }}
      >
        <div
          className="h-full transition-all duration-150"
          style={{
            width: `${progress}%`,
            backgroundColor: progress >= 100 ? COLORS.warning : COLORS.accent,
          }}
        />
      </div>
    </div>
  );
}
