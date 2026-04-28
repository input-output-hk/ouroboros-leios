import { FC } from "react";

import { useSimContext } from "@/contexts/SimContext/context";
import { EServerMessageType } from "../types";
import { EMessageColor } from "@/utils/colors";

const EVENT_TYPE_COLOR: Partial<Record<EServerMessageType, string>> = {
  [EServerMessageType.TransactionGenerated]: EMessageColor.TX,
  [EServerMessageType.TransactionSent]: EMessageColor.TX,
  [EServerMessageType.TransactionReceived]: EMessageColor.TX,
  [EServerMessageType.EBGenerated]: EMessageColor.EB,
  [EServerMessageType.EBSent]: EMessageColor.EB,
  [EServerMessageType.EBReceived]: EMessageColor.EB,
  [EServerMessageType.RBGenerated]: EMessageColor.RB,
  [EServerMessageType.RBSent]: EMessageColor.RB,
  [EServerMessageType.RBReceived]: EMessageColor.RB,
  [EServerMessageType.VotesGenerated]: EMessageColor.VOTES,
  [EServerMessageType.VotesSent]: EMessageColor.VOTES,
  [EServerMessageType.VotesReceived]: EMessageColor.VOTES,
};

export const Stats: FC = () => {
  const {
    state: { aggregatedData, events, currentTime },
  } = useSimContext();

  const formatTimeAsISO8601 = (timeInSeconds: number): string => {
    const date = new Date(timeInSeconds * 1000);
    return date.toISOString().replace("T", " ").replace("Z", "");
  };

  return (
    <div
      className={`flex flex-col gap-4 backdrop-blur-xs bg-white/80 min-w-[300px]`}
    >
      <div className="border-2 border-gray-200 rounded-sm p-4">
        <h4 className="font-bold uppercase mb-2">Global Stats</h4>

        <h4 className="flex items-center justify-between gap-4">
          Loaded Events: <span>{events.length}</span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Current Time:{" "}
          <span className="min-w-[200px] text-right">
            {formatTimeAsISO8601(currentTime)}
          </span>
        </h4>
        <h4 className="flex items-center justify-between gap-4">
          Events at Time: <span>{aggregatedData.eventCounts.total}</span>
        </h4>
        <br />
        {aggregatedData.eventCounts.total > 0 && (
          <>
            <h4 className="font-semibold">Event Types</h4>
            <div className="text-sm mt-2">
              {Object.values(EServerMessageType)
                .filter((eventType) => {
                  const count = aggregatedData.eventCounts.byType[eventType];
                  return (count || 0) > 0;
                })
                .map((eventType) => {
                  const count = aggregatedData.eventCounts.byType[eventType];
                  const isTxReceived =
                    eventType === EServerMessageType.TransactionReceived;

                  return (
                    <div
                      key={eventType}
                      className="flex justify-between text-sm items-center"
                    >
                      <span className="flex items-center gap-1">
                        {EVENT_TYPE_COLOR[eventType] && (
                          <span
                            className="inline-block w-2.5 h-2.5 rounded-sm flex-shrink-0"
                            style={{ backgroundColor: EVENT_TYPE_COLOR[eventType] }}
                          />
                        )}
                        {eventType}:
                        {isTxReceived && (
                          <span
                            className="text-yellow-600 text-xs font-bold cursor-help"
                            title="Transaction IDs are incomplete and may lead to inaccurate numbers and visualization"
                          >
                            ⚠️
                          </span>
                        )}
                      </span>
                      <span>{count || 0}</span>
                    </div>
                  );
                })}
            </div>
          </>
        )}
      </div>
    </div>
  );
};
