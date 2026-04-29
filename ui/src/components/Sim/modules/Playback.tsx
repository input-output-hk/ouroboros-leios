import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useCallback, useEffect, useRef } from "react";
import { Button } from "@/components/Button";
import { EConnectionState } from "@/contexts/SimContext/types";

const SPEED_OPTIONS = [0.01, 0.1, 0.25, 0.5, 1, 2, 4, 8];

export const Playback: FC = () => {
  const {
    state: {
      events,
      isPlaying,
      speedMultiplier,
      currentTime,
      maxTime,
      lokiConnectionState,
    },
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
      // Pause playback when seeking
      if (isPlaying) {
        dispatch({ type: "SET_TIMELINE_PLAYING", payload: false });
      }

      const maxEventTime =
        events.length > 0 ? events[events.length - 1].time_s : maxTime;
      const newTime = Math.max(
        0,
        Math.min(currentTime + stepAmount, maxEventTime),
      );
      dispatch({ type: "SET_TIMELINE_TIME", payload: newTime });
    },
    [dispatch, events, maxTime, currentTime, isPlaying],
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

      // Pause playback when seeking starts
      if (isPlaying) {
        dispatch({ type: "SET_TIMELINE_PLAYING", payload: false });
      }

      // Initial step using current context values
      handleStep(stepAmount);

      // Start continuous seeking after delay using stable callback
      stepTimeoutRef.current = window.setTimeout(() => {
        stepIntervalRef.current = window.setInterval(() => {
          handleStepForSeeking(stepAmount);
        }, 33); // ~30 FPS smooth seeking
      }, 300); // initial delay
    },
    [handleStep, handleStepForSeeking, stopSeeking, isPlaying, dispatch],
  );

  // Skip to next/previous event
  const handleSkipEvent = useCallback(
    (direction: 1 | -1) => {
      if (isPlaying) {
        dispatch({ type: "SET_TIMELINE_PLAYING", payload: false });
      }
      if (events.length === 0) return;

      if (direction === 1) {
        // Find first event after currentTime
        for (let i = 0; i < events.length; i++) {
          if (events[i].time_s > currentTime) {
            dispatch({ type: "SET_TIMELINE_TIME", payload: events[i].time_s });
            return;
          }
        }
      } else {
        // Find last event before currentTime
        for (let i = events.length - 1; i >= 0; i--) {
          if (events[i].time_s < currentTime) {
            dispatch({ type: "SET_TIMELINE_TIME", payload: events[i].time_s });
            return;
          }
        }
      }
    },
    [dispatch, events, currentTime, isPlaying],
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

        // Auto-pause at the end (but only if we're not connected to live Loki)
        if (
          newTime >= maxEventTime &&
          lokiConnectionState !== EConnectionState.Connected
        ) {
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
  const stepBackwardRef = useRef<HTMLButtonElement>(null);
  const stepForwardRef = useRef<HTMLButtonElement>(null);
  const skipBackwardRef = useRef<HTMLButtonElement>(null);
  const skipForwardRef = useRef<HTMLButtonElement>(null);
  const speedSelectRef = useRef<HTMLSelectElement>(null);

  const focusButton = (ref: React.RefObject<HTMLElement | null>) => {
    ref.current?.focus();
    setTimeout(() => {
      ref.current?.blur();
    }, 200); // Show focus for 200ms
  };

  const stepSize = speedMultiplier;

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
            focusButton(skipForwardRef);
            handleSkipEvent(1);
          } else {
            focusButton(stepForwardRef);
            handleStep(stepSize);
          }
          break;
        case "ArrowLeft":
          event.preventDefault();
          if (event.ctrlKey) {
            focusButton(skipBackwardRef);
            handleSkipEvent(-1);
          } else {
            focusButton(stepBackwardRef);
            handleStep(-stepSize);
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
  }, [disabled, handlePlayPause, handleStep, handleSkipEvent, stepSize, speedMultiplier, dispatch]);

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
        ref={skipBackwardRef}
        onClick={() => handleSkipEvent(-1)}
        disabled={disabled}
        variant="secondary"
        title="Skip to previous event (Ctrl + ←)"
      >
        ⏮
      </Button>

      <Button
        ref={stepBackwardRef}
        onMouseDown={(e) => {
          e.preventDefault();
          startSeeking(-stepSize);
        }}
        onMouseUp={(e) => {
          e.preventDefault();
          stopSeeking();
        }}
        onMouseLeave={stopSeeking}
        disabled={disabled}
        variant="secondary"
        title={`Step backward ${stepSize}s (←)`}
      >
        ◀
      </Button>

      <Button
        ref={stepForwardRef}
        onMouseDown={(e) => {
          e.preventDefault();
          startSeeking(stepSize);
        }}
        onMouseUp={(e) => {
          e.preventDefault();
          stopSeeking();
        }}
        onMouseLeave={stopSeeking}
        disabled={disabled}
        variant="secondary"
        title={`Step forward ${stepSize}s (→)`}
      >
        ▶
      </Button>

      <Button
        ref={skipForwardRef}
        onClick={() => handleSkipEvent(1)}
        disabled={disabled}
        variant="secondary"
        title="Skip to next event (Ctrl + →)"
      >
        ⏭
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
