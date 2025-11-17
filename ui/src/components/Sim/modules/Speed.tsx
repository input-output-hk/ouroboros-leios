import { useSimContext } from "@/contexts/SimContext/context";
import { FC, useCallback, useMemo } from "react";

export const Speed: FC = () => {
  const {
    state: { events },
  } = useSimContext();

  // For now, just show placeholder - implementation will come later
  const timelinePlaybackSpeed = useMemo(() => 1, []);

  const handleSpeedChange = useCallback(
    (event: React.ChangeEvent<HTMLSelectElement>) => {
      const newSpeed = parseFloat(event.target.value);
      // TODO: Implement timeline playback speed
      console.log("Timeline playback speed:", newSpeed);
    },
    []
  );

  return (
    <div className="min-w-32">
      <label htmlFor="timelineSpeed" className="block text-xs text-gray-600">
        Playback Speed
      </label>
      <select
        name="timelineSpeed"
        className="mt-1 w-full text-lg"
        value={timelinePlaybackSpeed}
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
  );
};
