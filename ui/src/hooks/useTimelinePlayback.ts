import { useSimContext } from "@/contexts/SimContext/context";
import { useEffect, useRef } from "react";

export const useTimelinePlayback = () => {
  const {
    state: { events, currentTime, isPlaying, speedMultiplier },
    dispatch,
  } = useSimContext();

  const intervalRef = useRef<number | null>(null);
  const lastUpdateRef = useRef<number>(0);

  useEffect(() => {
    if (isPlaying && events.length > 0) {
      const maxTime = events[events.length - 1].time_s;

      // Clear any existing interval
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
      }

      // Start playback interval
      // @ts-ignore
      intervalRef.current = setInterval(() => {
        const now = performance.now();
        // Convert to seconds and apply speed
        const deltaTime =
          ((now - lastUpdateRef.current) / 1000) * speedMultiplier;
        lastUpdateRef.current = now;

        dispatch({
          type: "SET_TIMELINE_TIME",
          payload: Math.min(currentTime + deltaTime, maxTime),
        });

        // Auto-pause at the end
        if (currentTime >= maxTime) {
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

  // Reset lastUpdate when currentTime changes externally (e.g., slider)
  useEffect(() => {
    lastUpdateRef.current = performance.now();
  }, [currentTime]);
};
