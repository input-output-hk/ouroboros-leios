import { useGraphContext } from "@/contexts/GraphContext/context";
import { type FC } from "react";

/** Built with AI !! */
export const Slider: FC = () => {
  const {
    state: { aggregatedData, maxTime },
  } = useGraphContext();

  return (
    <div className="w-full mx-auto p-4">
      Progress: {Math.floor(aggregatedData.progress * 100)}%
      <div
        className="relative w-full h-12 cursor-pointer"
        draggable={false}
        onDragStart={(e) => e.preventDefault()}
      >
        {/* Track */}
        <div className="absolute top-1/2 left-0 w-full h-2 -mt-1 rounded-full bg-gray-200">
          {/* Filled portion */}
          <div
            className="absolute h-full rounded-full bg-blue-500"
            style={{ width: `${aggregatedData.progress * 100}%` }}
          />
        </div>
      </div>
    </div>
  );
};
