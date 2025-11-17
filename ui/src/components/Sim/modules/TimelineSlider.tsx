import { useSimContext } from "@/contexts/SimContext/context";
import { type FC, useCallback, useMemo } from "react";

export const TimelineSlider: FC = () => {
  const {
    state: { events, currentTime },
    dispatch,
  } = useSimContext();

  const handleTimeChange = useCallback(
    (event: React.ChangeEvent<HTMLInputElement>) => {
      const newTime = parseFloat(event.target.value);
      dispatch({ type: "SET_TIMELINE_TIME", payload: newTime });
    },
    [dispatch],
  );

  // Don't render if no events loaded
  if (events.length === 0) {
    return null;
  }

  const maxTime = events[events.length - 1].time_s;

  const formatTime = (timeInSeconds: number) => {
    const minutes = Math.floor(timeInSeconds / 60);
    const seconds = (timeInSeconds % 60).toFixed(1);
    return minutes ? `${minutes}m${seconds}s` : `${seconds}s`;
  };

  const currentPercent = maxTime > 0 ? (currentTime / maxTime) * 100 : 0;

  return (
    <div className="w-full mx-auto px-4 flex flex-col items-between justify-center">
      <div className="relative w-full">
        {/* Track */}
        <div className="absolute top-1/2 left-0 w-full h-2 -mt-1 rounded-full bg-gray-200">
          {/* Filled portion */}
          <div
            className="absolute h-full rounded-full bg-green-500"
            style={{ width: `${currentPercent}%` }}
          />
        </div>

        {/* Interactive slider */}
        <input
          type="range"
          min={0}
          max={maxTime}
          step={0.1}
          value={currentTime}
          onChange={handleTimeChange}
          className="relative w-full h-2 bg-transparent appearance-none cursor-pointer z-10"
          style={{
            background: "transparent",
          }}
        />
      </div>

      <div className="flex justify-between text-xs text-gray-500 mt-1">
        <span>0s</span>
        <span>{formatTime(maxTime)}</span>
      </div>
    </div>
  );
};
