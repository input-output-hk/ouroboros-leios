import { FC, memo } from "react";

import { useGraphContext } from "@/contexts/GraphContext/context";
import { ESpeedOptions } from "@/contexts/GraphContext/types";
import { useHandlers } from "../hooks/useHandlers";

export const Controls: FC = memo(() => {
  const { playing, speed, setSpeed, setCurrentTime } = useGraphContext();
  const { handleResetSim } = useHandlers();
  return (
    <>
      <button
        className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
        // onClick={togglePlayPause}
      >
        {playing ? "Pause" : "Play"}
      </button>
      <button
        disabled={playing}
        className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
        onClick={handleResetSim}
      >
        Reset
      </button>
      <button onClick={(() => {
        setCurrentTime(1000)
      })}>
        Jump to Time
      </button>
      <div className="flex items-center justify-center gap-2">
        <label htmlFor="speed">Speed:</label>
        <select
          id="speed"
          disabled={playing}
          value={speed}
          onChange={(e) => {
            handleResetSim();
            setSpeed(Number(e.target.value) as ESpeedOptions);
          }}
        >
          {Object.keys(ESpeedOptions)
            .filter((key) => isNaN(Number(key)))
            .map((name) => {
              return (
                <option
                  key={name}
                  value={ESpeedOptions[name as keyof typeof ESpeedOptions]}
                >
                  {name}
                </option>
              );
            })}
        </select>
      </div>
    </>
  );
});
