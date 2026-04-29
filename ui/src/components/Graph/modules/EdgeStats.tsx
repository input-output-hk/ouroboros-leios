import { useSimContext } from "@/contexts/SimContext/context";
import { EMessageType, IMessageAnimation } from "@/contexts/SimContext/types";
import { EMessageColor } from "@/utils/colors";
import { FC, useMemo, useState } from "react";

const messageTypeColor: Record<EMessageType, string> = {
  [EMessageType.Txs]: EMessageColor.TXS,
  [EMessageType.EB]: EMessageColor.EB,
  [EMessageType.Votes]: EMessageColor.VOTES,
  [EMessageType.RB]: EMessageColor.RB,
};

const messageTypeLabel: Record<EMessageType, string> = {
  [EMessageType.Txs]: "Tx",
  [EMessageType.EB]: "EB",
  [EMessageType.Votes]: "Vote",
  [EMessageType.RB]: "RB",
};

const shortBits = (bytes: number): string => {
  const bits = bytes * 8;
  if (bits >= 1e9) return `${+(bits / 1e9).toPrecision(3)}Gb`;
  if (bits >= 1e6) return `${+(bits / 1e6).toPrecision(3)}Mb`;
  if (bits >= 1e3) return `${+(bits / 1e3).toPrecision(3)}kb`;
  return `${bits}b`;
};

const shortBytes = (bytes: number): string => {
  if (bytes >= 1e9) return `${+(bytes / 1e9).toPrecision(3)}GB`;
  if (bytes >= 1e6) return `${+(bytes / 1e6).toPrecision(3)}MB`;
  if (bytes >= 1e3) return `${+(bytes / 1e3).toPrecision(3)}kB`;
  return `${bytes}B`;
};

// Extract the original message id from the animation key (id-sender-recipient)
const getMessageId = (animation: IMessageAnimation): string => {
  const suffix = `-${animation.sender}-${animation.recipient}`;
  return animation.id.endsWith(suffix)
    ? animation.id.slice(0, -suffix.length)
    : animation.id;
};

const MessageDetail: FC<{
  animation: IMessageAnimation;
}> = ({ animation }) => {
  const msgId = getMessageId(animation);

  const details: { label: string; value: string }[] = [
    { label: "Id", value: msgId },
    { label: "Sent at", value: `${animation.sentTime.toFixed(3)}s` },
  ];

  if (animation.type !== EMessageType.Votes && animation.slot) {
    details.push({ label: "Slot", value: String(animation.slot) });
  }

  // Vote-specific details
  if (animation.votes && animation.votes.length > 0) {
    const rounds = [...new Set(animation.votes.map((v) => v.electionId))];
    details.push({ label: "Round", value: rounds.join(", ") });

    const ebHashes = [...new Set(animation.votes.map((v) => v.ebHash))];
    details.push({ label: "EB hash", value: ebHashes.join(", ") });

    const voterIds = [...new Set(animation.votes.map((v) => v.voterId))];
    details.push({ label: "Voter", value: voterIds.join(", ") });

    if (animation.votes.length > 1) {
      details.push({ label: "Num votes", value: String(animation.votes.length) });
    }
  }

  if (animation.numTxs != null && animation.numTxs > 0) {
    details.push({ label: "Num txs", value: String(animation.numTxs) });
  }

  return (
    <div className="text-xs border-t border-gray-200 pt-2 mt-2 space-y-0.5">
      {details.map(({ label, value }) => (
        <div key={label} className="flex justify-between gap-4">
          <span className="text-gray-500">{label}</span>
          <span className="font-mono truncate max-w-[200px] text-right">{value}</span>
        </div>
      ))}
    </div>
  );
};

export const EdgeStats: FC = () => {
  const {
    state: {
      aggregatedData,
      graph: { currentEdge },
      topography,
    },
  } = useSimContext();

  const [userSelectedId, setUserSelectedId] = useState<string | null>(null);

  const link = useMemo(() => {
    if (!currentEdge) return undefined;
    return topography.links.get(currentEdge);
  }, [currentEdge, topography.links]);

  const messagesOnEdge = useMemo(() => {
    if (!currentEdge) return [];
    const [source, target] = currentEdge.split("|");
    return aggregatedData.messages
      .filter((m) => {
        const key = [m.sender, m.recipient].sort().join("|");
        return key === currentEdge;
      })
      .map((m) => ({
        ...m,
        direction:
          m.sender === source
            ? `${source} \u2192 ${target}`
            : `${target} \u2192 ${source}`,
      }));
  }, [currentEdge, aggregatedData.messages]);

  const selectedMessageId = useMemo(() => {
    // If user clicked a row that still exists, use that
    if (userSelectedId && messagesOnEdge.some((m) => m.id === userSelectedId)) {
      return userSelectedId;
    }
    // Otherwise default to first message
    return messagesOnEdge[0]?.id ?? null;
  }, [userSelectedId, messagesOnEdge]);

  const selectedMessage = useMemo(() => {
    if (!selectedMessageId) return null;
    return messagesOnEdge.find((m) => m.id === selectedMessageId) ?? null;
  }, [selectedMessageId, messagesOnEdge]);

  if (!currentEdge || !link) return null;

  const [source, target] = currentEdge.split("|");

  return (
    <div className="border-2 border-gray-200 rounded-sm p-4 z-30 bg-white/80 backdrop-blur-xs min-w-[320px] block">
      <h2 className="flex items-center justify-between gap-4 font-bold uppercase mb-2">
        Edge Stats
      </h2>
      <div className="text-sm mb-3">
        <span className="text-gray-600">{source}</span>
        {" <-> "}
        <span className="text-gray-600">{target}</span>
      </div>

      {link.latencyMs != null && (
        <div className="text-sm mb-1">
          <span className="text-gray-500">Latency:</span>{" "}
          <span className="font-mono">{link.latencyMs}ms</span>
        </div>
      )}
      {link.bandwidthBytesPerSecond != null && (
        <div className="text-sm mb-3">
          <span className="text-gray-500">Bandwidth:</span>{" "}
          <span className="font-mono">
            {shortBits(link.bandwidthBytesPerSecond)}/s
          </span>
        </div>
      )}

      {messagesOnEdge.length === 0 ? (
        <p className="text-xs text-gray-400">No messages in transit</p>
      ) : (
        <>
          <table className="w-full text-xs">
            <thead>
              <tr className="text-gray-500 border-b">
                <th className="text-left py-0.5">Type</th>
                <th className="text-left py-0.5">Direction</th>
                <th className="text-right py-0.5">Size</th>
                <th className="text-right py-0.5">Done</th>
              </tr>
            </thead>
            <tbody>
              {messagesOnEdge.map((m) => {
                const color = messageTypeColor[m.type];
                const isSelected = m.id === selectedMessage?.id;
                return (
                  <tr
                    key={m.id}
                    className={`border-b border-gray-100 cursor-pointer hover:bg-gray-100 ${isSelected ? "bg-gray-200" : ""}`}
                    onClick={() => setUserSelectedId(isSelected ? null : m.id)}
                  >
                    <td className="py-0.5">
                      <span className="flex items-center gap-1">
                        <span
                          className="inline-block w-2 h-2 rounded-full"
                          style={{ backgroundColor: color }}
                        />
                        {messageTypeLabel[m.type]}
                      </span>
                    </td>
                    <td className="py-0.5">{m.direction}</td>
                    <td className="py-0.5 text-right font-mono">
                      {shortBytes(m.sizeBytes)}
                    </td>
                    <td className="py-0.5 text-right font-mono">
                      {Math.round(m.progress * 100)}%
                    </td>
                  </tr>
                );
              })}
            </tbody>
          </table>

          {selectedMessage && (
            <MessageDetail animation={selectedMessage} />
          )}
        </>
      )}
    </div>
  );
};
