import { useSimContext } from "@/contexts/SimContext/context";
import { type FC, useCallback } from "react";

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

  const hasEvents = events.length > 0;
  const maxTime = hasEvents ? events[events.length - 1].time_s : 100; // Default duration when no events

  const formatTime = (timeInSeconds: number, highResolution = false) => {
    return highResolution
      ? `${timeInSeconds.toFixed(3)}s`
      : `${timeInSeconds.toFixed(1)}s`;
  };

  const currentPercent = maxTime > 0 ? (currentTime / maxTime) * 100 : 0;

  return (
    <div
      className={`w-full mx-auto flex flex-col items-between justify-center ${!hasEvents ? "opacity-50" : ""}`}
    >
      <div className="relative w-full">
        {/* Track */}
        <div className="absolute top-1/2 left-0 w-full h-2 -mt-1 rounded-full bg-gray-200">
          {/* Filled portion */}
          <div
            className={`absolute h-full rounded-full ${hasEvents ? "bg-green-500" : "bg-gray-400"}`}
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
          disabled={!hasEvents}
          className="relative w-full h-2 bg-transparent appearance-none cursor-pointer z-10 disabled:cursor-not-allowed"
          style={{
            background: "transparent",
          }}
        />
      </div>

      <div className="flex justify-start text-sm text-gray-600 mt-1">
        <span>
          {hasEvents ? formatTime(currentTime, true) : "0s"} /{" "}
          {hasEvents ? formatTime(maxTime) : "0s"}
        </span>
      </div>
    </div>
  );
};
