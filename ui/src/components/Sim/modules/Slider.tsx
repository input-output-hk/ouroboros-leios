import { useSimContext } from "@/contexts/SimContext/context";
import { type FC } from "react";

export const Progress: FC = () => {
  const {
    state: { aggregatedData, maxTime },
  } = useSimContext();

  const percent = (aggregatedData.progress / maxTime) * 100;

  const minutes = Math.floor(aggregatedData.progress / 60);
  const seconds = (aggregatedData.progress % 60).toFixed(3);
  const time = minutes ? `${minutes}m${seconds}s` : `${seconds}s`;

  return (
    <div className="w-full mx-auto px-4 flex flex-col items-between justify-center">
      <p className="mb-0">
        Time: {time}<br />
      </p>

      <div
        className="relative w-full mt-4"
      >
        {/* Track */}
        <div className="absolute top-1/2 left-0 w-full h-2 -mt-3 rounded-full bg-gray-200">
          {/* Filled portion */}
          <div
            className="absolute h-full rounded-full bg-blue-500"
            style={{ width: `${percent}%` }}
          />
        </div>
      </div>
    </div>
  );
};
