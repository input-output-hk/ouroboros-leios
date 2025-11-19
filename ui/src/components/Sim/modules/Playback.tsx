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
  const currentTimeRef = useRef<number>(currentTime);

  // Refs for seeking functionality
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
        eventsRef.current.length > 0
          ? eventsRef.current[eventsRef.current.length - 1].time_s
          : maxTimeRef.current;
      const currentTime = currentTimeRef.current;
      const newTime = Math.max(
        0,
        Math.min(currentTime + stepAmount, maxEventTime),
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

      // Initial step using current ref values
      handleStep(stepAmount);

      // Start continuous seeking after delay
      stepTimeoutRef.current = window.setTimeout(() => {
        stepIntervalRef.current = window.setInterval(() => {
          handleStep(stepAmount);
        }, 33); // ~30 FPS smooth seeking
      }, 300); // initial delay
    },
    [handleStep, stopSeeking],
  );

  // Timeline playback effect - handles automatic advancement when playing
  useEffect(() => {
    if (isPlaying && events.length > 0) {
      const maxEventTime = events[events.length - 1].time_s;

      // Clear any existing interval
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
      }

      // Start playback interval
      intervalRef.current = window.setInterval(() => {
        const now = performance.now();
        // Convert to seconds and apply speed
        const deltaTime =
          ((now - lastUpdateRef.current) / 1000) * speedMultiplier;
        lastUpdateRef.current = now;

        const newTime = Math.min(
          currentTimeRef.current + deltaTime,
          maxEventTime,
        );
        currentTimeRef.current = newTime;

        dispatch({
          type: "SET_TIMELINE_TIME",
          payload: newTime,
        });

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
  }, [
    isPlaying,
    events.length,
    currentTime,
    speedMultiplier,
    dispatch,
    stopSeeking,
  ]);

  // Keep refs in sync when values change externally
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

  // Keyboard event handler
  useEffect(() => {
    const handleKeyDown = (event: KeyboardEvent) => {
      if (disabled) return;

      switch (event.code) {
        case "Space":
          event.preventDefault();
          handlePlayPause();
          break;
        case "ArrowRight":
          event.preventDefault();
          if (event.ctrlKey) {
            handleStep(1.0 * speedMultiplier); // 10x forward (big step)
          } else {
            handleStep(0.1 * speedMultiplier); // 1x forward (small step)
          }
          break;
        case "ArrowLeft":
          event.preventDefault();
          if (event.ctrlKey) {
            handleStep(-1.0 * speedMultiplier); // 10x backward (big step)
          } else {
            handleStep(-0.1 * speedMultiplier); // 1x backward (small step)
          }
          break;
        case "ArrowUp":
          event.preventDefault();
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
        onClick={handlePlayPause}
        disabled={disabled}
        variant="primary"
        className="w-20"
        title={isPlaying ? "Pause (Space)" : "Play (Space)"}
      >
        {isPlaying ? "Pause" : "Play"}
      </Button>

      <Button
        onClick={() => handleStep(-1.0 * speedMultiplier)}
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
        size="sm"
        className="px-2"
        title={`Step backward ${1.0 * speedMultiplier}s (Ctrl + ←)`}
      >
        &lt;&lt;
      </Button>

      <Button
        onClick={() => handleStep(-0.1 * speedMultiplier)}
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
        size="sm"
        className="px-2"
        title={`Step backward ${0.1 * speedMultiplier}s (←)`}
      >
        &lt;
      </Button>

      <Button
        onClick={() => handleStep(0.1 * speedMultiplier)}
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
        size="sm"
        className="px-2"
        title={`Step forward ${0.1 * speedMultiplier}s (→)`}
      >
        &gt;
      </Button>

      <Button
        onClick={() => handleStep(1.0 * speedMultiplier)}
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
        size="sm"
        className="px-2"
        title={`Step forward ${1.0 * speedMultiplier}s (Ctrl + →)`}
      >
        &gt;&gt;
      </Button>

      <div className="min-w-16">
        <label htmlFor="timelineSpeed" className="block text-xs text-gray-600">
          Speed
        </label>
        <select
          name="timelineSpeed"
          className="mt-1 w-full text-sm"
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
    </div>
  );
};
