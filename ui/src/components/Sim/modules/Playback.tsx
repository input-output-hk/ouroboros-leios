import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useCallback } from "react";

export const Playback: FC = () => {
  const {
    state: { events, isPlaying, speedMultiplier },
    dispatch,
  } = useSimContext();

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

  return (
    <div className="flex items-end gap-4">
      <button
        onClick={handlePlayPause}
        disabled={events.length === 0}
        className="bg-blue-500 text-white px-3 py-2 rounded disabled:bg-gray-300 disabled:cursor-not-allowed w-20"
      >
        {isPlaying ? "Pause" : "Play"}
      </button>

      <div className="min-w-16">
        <label htmlFor="timelineSpeed" className="block text-xs text-gray-600">
          Speed
        </label>
        <select
          name="timelineSpeed"
          className="mt-1 w-full text-lg"
          value={speedMultiplier}
          onChange={handleSpeedChange}
          disabled={events.length === 0}
        >
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
