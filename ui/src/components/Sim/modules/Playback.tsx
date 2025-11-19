import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useCallback, useEffect, useRef } from "react";
import { Button } from "@/components/Button";

export const Playback: FC = () => {
  const {
    state: { events, isPlaying, speedMultiplier, currentTime, maxTime },
    dispatch,
  } = useSimContext();

  // Timeline playback refs
  const intervalRef = useRef<number | null>(null);
  const lastUpdateRef = useRef<number>(0);
  const currentTimeRef = useRef<number>(currentTime);

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
    [dispatch, currentTime, events, maxTime],
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

    // Cleanup on unmount
    return () => {
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
      }
    };
  }, [isPlaying, events.length, currentTime, speedMultiplier, dispatch]);

  // Keep currentTimeRef in sync when currentTime changes externally (e.g., slider)
  useEffect(() => {
    currentTimeRef.current = currentTime;
    lastUpdateRef.current = performance.now();
  }, [currentTime]);

  const disabled = events.length === 0;

  return (
    <div className="flex items-center gap-2">
      {/* Play/Pause button */}
      <Button
        onClick={handlePlayPause}
        disabled={disabled}
        variant="primary"
        className="w-20"
      >
        {isPlaying ? "Pause" : "Play"}
      </Button>

      {/* Step controls: << < > >> */}
      <Button
        onClick={() => handleStep(-0.01)}
        disabled={disabled}
        variant="secondary"
        size="sm"
        className="px-2"
        title="Step backward 10ms"
      >
        &lt;&lt;
      </Button>

      <Button
        onClick={() => handleStep(-0.001)}
        disabled={disabled}
        variant="secondary"
        size="sm"
        className="px-2"
        title="Step backward 1ms"
      >
        &lt;
      </Button>

      <Button
        onClick={() => handleStep(0.001)}
        disabled={disabled}
        variant="secondary"
        size="sm"
        className="px-2"
        title="Step forward 1ms"
      >
        &gt;
      </Button>

      <Button
        onClick={() => handleStep(0.01)}
        disabled={disabled}
        variant="secondary"
        size="sm"
        className="px-2"
        title="Step forward 10ms"
      >
        &gt;&gt;
      </Button>

      {/* Speed control */}
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
        >
          <option value={0.01}>0.01x</option>
          <option value={0.1}>0.1x</option>
          <option value={0.25}>0.25x</option>
          <option value={0.5}>0.5x</option>
          <option value={1}>1x</option>
          <option value={2}>2x</option>
          <option value={4}>4x</option>
          <option value={8}>8x</option>
        </select>
      </div>
    </div>
  );
};
