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

  const handleStepBackward10ms = useCallback(() => {
    dispatch({ type: "STEP_TIMELINE_BACKWARD", payload: 0.01 });
  }, [dispatch]);

  const handleStepBackward1ms = useCallback(() => {
    dispatch({ type: "STEP_TIMELINE_BACKWARD", payload: 0.001 });
  }, [dispatch]);

  const handleStepForward1ms = useCallback(() => {
    dispatch({ type: "STEP_TIMELINE_FORWARD", payload: 0.001 });
  }, [dispatch]);

  const handleStepForward10ms = useCallback(() => {
    dispatch({ type: "STEP_TIMELINE_FORWARD", payload: 0.01 });
  }, [dispatch]);

  const disabled = events.length === 0;

  return (
    <div className="flex items-center gap-2">
      {/* Play/Pause button */}
      <button
        onClick={handlePlayPause}
        disabled={disabled}
        className="bg-blue-500 text-white px-3 py-2 rounded disabled:bg-gray-300 disabled:cursor-not-allowed w-16 text-sm"
      >
        {isPlaying ? "Pause" : "Play"}
      </button>

      {/* Step controls: << < > >> */}
      <button
        onClick={handleStepBackward10ms}
        disabled={disabled}
        className="bg-gray-500 text-white px-2 py-2 rounded disabled:bg-gray-300 disabled:cursor-not-allowed text-sm"
        title="Step backward 10ms"
      >
        &lt;&lt;
      </button>

      <button
        onClick={handleStepBackward1ms}
        disabled={disabled}
        className="bg-gray-500 text-white px-2 py-2 rounded disabled:bg-gray-300 disabled:cursor-not-allowed text-sm"
        title="Step backward 1ms"
      >
        &lt;
      </button>

      <button
        onClick={handleStepForward1ms}
        disabled={disabled}
        className="bg-gray-500 text-white px-2 py-2 rounded disabled:bg-gray-300 disabled:cursor-not-allowed text-sm"
        title="Step forward 1ms"
      >
        &gt;
      </button>

      <button
        onClick={handleStepForward10ms}
        disabled={disabled}
        className="bg-gray-500 text-white px-2 py-2 rounded disabled:bg-gray-300 disabled:cursor-not-allowed text-sm"
        title="Step forward 10ms"
      >
        &gt;&gt;
      </button>

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
