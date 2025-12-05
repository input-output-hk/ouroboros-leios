import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useCallback, useEffect, useRef } from "react";
import { Button } from "@/components/Button";

const SPEED_OPTIONS = [0.01, 0.1, 0.25, 0.5, 1, 2, 4, 8];

export const Playback: FC = () => {
  const {
    state: { events, isPlaying, speedMultiplier, currentTime, maxTime },
    dispatch,
  } = useSimContext();

  // Timeline playback refs
  const intervalRef = useRef<number | null>(null);
  const lastUpdateRef = useRef<number>(0);

  // Refs for stable seeking callbacks
  const currentTimeRef = useRef(currentTime);
  const eventsRef = useRef(events);
  const maxTimeRef = useRef(maxTime);

  const handleSpeedChange = useCallback(
    (event: React.ChangeEvent<HTMLSelectElement>) => {
      const newSpeed = parseFloat(event.target.value);
      dispatch({ type: "SET_TIMELINE_SPEED", payload: newSpeed });
    },
    [dispatch],
  );

  const handlePlayPause = useCallback(() => {
    dispatch({ type: "SET_TIMELINE_PLAYING", payload: !isPlaying });
  }, [dispatch, isPlaying]);

  // Press-to-seek refs
  const stepIntervalRef = useRef<number | null>(null);
  const stepTimeoutRef = useRef<number | null>(null);

  const stopSeeking = useCallback(() => {
    if (stepTimeoutRef.current) {
      clearTimeout(stepTimeoutRef.current);
      stepTimeoutRef.current = null;
    }
    if (stepIntervalRef.current) {
      clearInterval(stepIntervalRef.current);
      stepIntervalRef.current = null;
    }
  }, []);

  const handleStep = useCallback(
    (stepAmount: number) => {
      const maxEventTime =
        events.length > 0 ? events[events.length - 1].time_s : maxTime;
      const newTime = Math.max(
        0,
        Math.min(currentTime + stepAmount, maxEventTime),
      );
      dispatch({ type: "SET_TIMELINE_TIME", payload: newTime });
    },
    [dispatch, events, maxTime, currentTime],
  );

  // Stable version for seeking intervals (uses refs)
  const handleStepForSeeking = useCallback(
    (stepAmount: number) => {
      const maxEventTime =
        eventsRef.current.length > 0
          ? eventsRef.current[eventsRef.current.length - 1].time_s
          : maxTimeRef.current;
      const newTime = Math.max(
        0,
        Math.min(currentTimeRef.current + stepAmount, maxEventTime),
      );
      currentTimeRef.current = newTime;
      dispatch({ type: "SET_TIMELINE_TIME", payload: newTime });
    },
    [dispatch],
  );

  const startSeeking = useCallback(
    (stepAmount: number) => {
      // Clear any existing seeking first
      stopSeeking();

      // Initial step using current context values
      handleStep(stepAmount);

      // Start continuous seeking after delay using stable callback
      stepTimeoutRef.current = window.setTimeout(() => {
        stepIntervalRef.current = window.setInterval(() => {
          handleStepForSeeking(stepAmount);
        }, 33); // ~30 FPS smooth seeking
      }, 300); // initial delay
    },
    [handleStep, handleStepForSeeking, stopSeeking],
  );

  // Timeline playback effect - handles automatic advancement when playing
  useEffect(() => {
    if (isPlaying && events.length > 0) {
      const maxEventTime = events[events.length - 1].time_s;

      // Clear any existing interval
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
      }

      // Capture current time at interval start to avoid stale closure
      let localCurrentTime = currentTime;

      // Start playback interval
      intervalRef.current = window.setInterval(() => {
        const now = performance.now();
        // Convert to seconds and apply speed
        const deltaTime =
          ((now - lastUpdateRef.current) / 1000) * speedMultiplier;
        lastUpdateRef.current = now;

        const newTime = Math.min(localCurrentTime + deltaTime, maxEventTime);
        localCurrentTime = newTime;

        dispatch({ type: "SET_TIMELINE_TIME", payload: newTime });

        // Auto-pause at the end
        if (newTime >= maxEventTime) {
          dispatch({ type: "SET_TIMELINE_PLAYING", payload: false });
        }
      }, 16); // ~60 FPS

      lastUpdateRef.current = performance.now();
    } else {
      // Clear interval when paused or no events
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
        intervalRef.current = null;
      }
    }
  }, [isPlaying, events.length, speedMultiplier, dispatch]);

  // Keep refs in sync with context values
  useEffect(() => {
    currentTimeRef.current = currentTime;
    lastUpdateRef.current = performance.now();
  }, [currentTime]);

  useEffect(() => {
    eventsRef.current = events;
  }, [events]);

  useEffect(() => {
    maxTimeRef.current = maxTime;
  }, [maxTime]);

  const disabled = events.length === 0;

  // Button refs for focus management
  const playPauseRef = useRef<HTMLButtonElement>(null);
  const stepSmallBackwardRef = useRef<HTMLButtonElement>(null);
  const stepBigBackwardRef = useRef<HTMLButtonElement>(null);
  const stepSmallForwardRef = useRef<HTMLButtonElement>(null);
  const stepBigForwardRef = useRef<HTMLButtonElement>(null);
  const speedSelectRef = useRef<HTMLSelectElement>(null);

  const focusButton = (ref: React.RefObject<HTMLElement | null>) => {
    ref.current?.focus();
    setTimeout(() => {
      ref.current?.blur();
    }, 200); // Show focus for 200ms
  };

  // Keyboard event handler
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      if (disabled) return;

      switch (event.code) {
        case "Space":
          event.preventDefault();
          focusButton(playPauseRef);
          handlePlayPause();
          break;
        case "ArrowRight":
          event.preventDefault();
          if (event.ctrlKey) {
            focusButton(stepBigForwardRef);
            handleStep(1.0 * speedMultiplier); // 10x forward (big step)
          } else {
            focusButton(stepSmallForwardRef);
            handleStep(0.1 * speedMultiplier); // 1x forward (small step)
          }
          break;
        case "ArrowLeft":
          event.preventDefault();
          if (event.ctrlKey) {
            focusButton(stepBigBackwardRef);
            handleStep(-1.0 * speedMultiplier); // 10x backward (big step)
          } else {
            focusButton(stepSmallBackwardRef);
            handleStep(-0.1 * speedMultiplier); // 1x backward (small step)
          }
          break;
        case "ArrowUp":
          event.preventDefault();
          focusButton(speedSelectRef);
          // Increase speed to next available option
          {
            const currentIndex = SPEED_OPTIONS.indexOf(speedMultiplier);
            if (currentIndex < SPEED_OPTIONS.length - 1) {
              dispatch({
                type: "SET_TIMELINE_SPEED",
                payload: SPEED_OPTIONS[currentIndex + 1],
              });
            }
          }
          break;
        case "ArrowDown":
          event.preventDefault();
          focusButton(speedSelectRef);
          // Decrease speed to previous available option
          {
            const currentIndex = SPEED_OPTIONS.indexOf(speedMultiplier);
            if (currentIndex > 0) {
              dispatch({
                type: "SET_TIMELINE_SPEED",
                payload: SPEED_OPTIONS[currentIndex - 1],
              });
            }
          }
          break;
      }
    };

    document.addEventListener("keydown", handleKeyDown);
    return () => document.removeEventListener("keydown", handleKeyDown);
  }, [disabled, handlePlayPause, handleStep, speedMultiplier, dispatch]);

  return (
    <div className="flex items-center gap-2">
      <Button
        ref={playPauseRef}
        onClick={handlePlayPause}
        disabled={disabled}
        variant="primary"
        className="w-20"
        title={isPlaying ? "Pause (Space)" : "Play (Space)"}
      >
        {isPlaying ? "Pause" : "Play"}
      </Button>

      <Button
        ref={stepBigBackwardRef}
        onMouseDown={(e) => {
          e.preventDefault();
          startSeeking(-1.0 * speedMultiplier);
        }}
        onMouseUp={(e) => {
          e.preventDefault();
          stopSeeking();
        }}
        onMouseLeave={stopSeeking}
        disabled={disabled}
        variant="secondary"
        title={`Step backward ${1.0 * speedMultiplier}s (Ctrl + ←)`}
      >
        ◀◀
      </Button>

      <Button
        ref={stepSmallBackwardRef}
        onMouseDown={(e) => {
          e.preventDefault();
          startSeeking(-0.1 * speedMultiplier);
        }}
        onMouseUp={(e) => {
          e.preventDefault();
          stopSeeking();
        }}
        onMouseLeave={stopSeeking}
        disabled={disabled}
        variant="secondary"
        title={`Step backward ${0.1 * speedMultiplier}s (←)`}
      >
        ◀
      </Button>

      <Button
        ref={stepSmallForwardRef}
        onMouseDown={(e) => {
          e.preventDefault();
          startSeeking(0.1 * speedMultiplier);
        }}
        onMouseUp={(e) => {
          e.preventDefault();
          stopSeeking();
        }}
        onMouseLeave={stopSeeking}
        disabled={disabled}
        variant="secondary"
        title={`Step forward ${0.1 * speedMultiplier}s (→)`}
      >
        ▶
      </Button>

      <Button
        ref={stepBigForwardRef}
        onMouseDown={(e) => {
          e.preventDefault();
          startSeeking(1.0 * speedMultiplier);
        }}
        onMouseUp={(e) => {
          e.preventDefault();
          stopSeeking();
        }}
        onMouseLeave={stopSeeking}
        disabled={disabled}
        variant="secondary"
        title={`Step forward ${1.0 * speedMultiplier}s (Ctrl + →)`}
      >
        ▶▶
      </Button>

      <select
        ref={speedSelectRef}
        name="timelineSpeed"
        className="min-w-16 rounded-md transition-all duration-150 bg-gray-600 hover:bg-gray-700 text-white focus:outline-none focus:ring-2 focus:ring-offset-2 focus:ring-gray-500 disabled:bg-gray-300 disabled:text-gray-500 px-2 py-2 cursor-pointer disabled:cursor-not-allowed"
        value={speedMultiplier}
        onChange={handleSpeedChange}
        disabled={disabled}
        title="Change speed (↑ / ↓)"
      >
        {SPEED_OPTIONS.map((speed) => (
          <option key={speed} value={speed}>
            {speed}x
          </option>
        ))}
      </select>
    </div>
  );
};
