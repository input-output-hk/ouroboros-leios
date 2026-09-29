import { Fragment, FC } from "react";

import { useSimContext } from "@/contexts/SimContext/context";
import { EServerMessageType } from "../types";
import { EMessageType } from "@/contexts/SimContext/types";
import { EMessageColor } from "@/utils/colors";

// One row per message type: the created/sent/received triple for each, rather
// than a flat list of every event kind. `created` is left off announcements and
// EB txs, whose cells stay blank -- neither has an origin event on the wire, so
// a zero there would claim none were seen when nothing is being counted.
type MessageGroup = {
  type: EMessageType;
  label: string;
  color: EMessageColor;
  created?: EServerMessageType;
  sent: EServerMessageType;
  received: EServerMessageType;
};

// Declared here, ordered by EMessageType below, so that enum stays the single
// place display order is decided (the per-node panel derives from it too).
const GROUP_ORDER = Object.values(EMessageType);

const MESSAGE_GROUPS: MessageGroup[] = [
  {
    type: EMessageType.Announcement,
    label: "Announcement",
    color: EMessageColor.ANNOUNCEMENT,
    sent: EServerMessageType.AnnouncementSent,
    received: EServerMessageType.AnnouncementReceived,
  },
  {
    type: EMessageType.EB,
    label: "Endorser Blocks",
    color: EMessageColor.EB,
    created: EServerMessageType.EBGenerated,
    sent: EServerMessageType.EBSent,
    received: EServerMessageType.EBReceived,
  },
  {
    type: EMessageType.Txs,
    // "Missing" because this row is the Leios closure-fetch path, which only
    // engages on a tx-cache miss: an EB names txs the node does not hold, so it
    // offers/fetches them. It is not how txs normally reach a mempool -- that
    // is TxSubmission, whose per-message traces the node currently silences
    // (TxSubmission.Remote is at Notice, the messages are Debug).
    label: "Missing Txs",
    color: EMessageColor.TXS,
    // No created column: nothing on the wire originates these. `TxsGenerated`
    // exists in the schema for simulator traces, but no Loki parser emits it,
    // so on a live devnet the cell would read a permanent 0.
    sent: EServerMessageType.TxsSent,
    received: EServerMessageType.TxsReceived,
  },
  {
    type: EMessageType.Votes,
    label: "Votes",
    color: EMessageColor.VOTES,
    // `LeiosVoted`, one per (rbHash, voterId) -- the unique votes cast. Note
    // the columns count different units on this row: sent/received come from
    // `MsgLeiosVotes`, and one such message carries a bundle of votes.
    created: EServerMessageType.VotesGenerated,
    sent: EServerMessageType.VotesSent,
    received: EServerMessageType.VotesReceived,
  },
  {
    type: EMessageType.RB,
    label: "Ranking Blocks",
    color: EMessageColor.RB,
    created: EServerMessageType.RBGenerated,
    sent: EServerMessageType.RBSent,
    received: EServerMessageType.RBReceived,
  },
].sort((a, b) => GROUP_ORDER.indexOf(a.type) - GROUP_ORDER.indexOf(b.type));

export const Stats: FC = () => {
  const {
    state: { aggregatedData, events, currentTime, lokiDroppedEntries },
  } = useSimContext();

  // Absent kinds read as 0 here; the render distinguishes "no such event type"
  // from "zero seen" by checking whether the kind is defined at all.
  const count = (eventType?: EServerMessageType): number =>
    eventType ? aggregatedData.eventCounts.byType[eventType] || 0 : 0;

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
        {lokiDroppedEntries > 0 && (
          <h4
            className="flex items-center justify-between gap-4 text-red-600"
            title="Entries Loki's tail handler dropped due to consumer backpressure"
          >
            Loki dropped: <span>{lokiDroppedEntries}</span>
          </h4>
        )}
        <br />
        {aggregatedData.eventCounts.total > 0 && (
          <>
            <h4 className="font-semibold">Event Types</h4>
            <div className="mt-2 grid grid-cols-[1fr_auto_auto_auto] gap-x-3 text-sm">
              <span />
              <span className="text-right text-xs uppercase text-gray-500">
                created
              </span>
              <span className="text-right text-xs uppercase text-gray-500">
                sent
              </span>
              <span className="text-right text-xs uppercase text-gray-500">
                received
              </span>
              {MESSAGE_GROUPS.filter(
                (group) =>
                  count(group.created) + count(group.sent) + count(group.received) >
                  0,
              ).map((group) => (
                <Fragment key={group.type}>
                  <span className="flex items-center gap-1">
                    <span
                      className="inline-block w-2.5 h-2.5 rounded-sm flex-shrink-0"
                      style={{ backgroundColor: group.color }}
                    />
                    {group.label}
                  </span>
                  <span className="text-right tabular-nums">
                    {group.created ? count(group.created) : ""}
                  </span>
                  <span className="text-right tabular-nums">
                    {count(group.sent)}
                  </span>
                  <span className="text-right tabular-nums">
                    {count(group.received)}
                  </span>
                </Fragment>
              ))}
            </div>
          </>
        )}
      </div>
    </div>
  );
};
