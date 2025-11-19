import { FC } from "react";

import { useSimContext } from "@/contexts/SimContext/context";
import { EServerMessageType } from "../types";

export const Stats: FC = () => {
  const {
    state: { aggregatedData, events, currentTime },
  } = useSimContext();

  return (
    <div
      className={`flex flex-col gap-4 backdrop-blur-xs bg-white/80 text-xl min-w-[300px]`}
    >
      <div className="border-2 border-gray-200 rounded-sm p-4">
        <h2 className="font-bold uppercase mb-2">Global Stats</h2>

        <div className="text-base">
          <h4 className="flex items-center justify-between gap-4">
            Loaded Events: <span>{events.length}</span>
          </h4>
          <h4 className="flex items-center justify-between gap-4">
            Current Time: <span>{currentTime.toFixed(2)}s</span>
          </h4>
          <h4 className="flex items-center justify-between gap-4">
            Events at Time: <span>{aggregatedData.eventCounts.total}</span>
          </h4>
          <br />
          <h4 className="font-semibold">Event Types</h4>
          {aggregatedData.eventCounts.total > 0 && (
            <div className="text-sm mt-2">
              {Object.values(EServerMessageType).map((eventType) => {
                const count = aggregatedData.eventCounts.byType[eventType];
                return (
                  <div key={eventType} className="flex justify-between text-sm">
                    <span>{eventType}:</span> <span>{count || 0}</span>
                  </div>
                );
              })}
            </div>
          )}
        </div>
      </div>
    </div>
  );
};
