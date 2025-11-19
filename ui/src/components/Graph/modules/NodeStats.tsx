import { useSimContext } from "@/contexts/SimContext/context";
import { EMessageType } from "@/contexts/SimContext/types";
import { printBytes } from "@/utils";
import { FC, useMemo } from "react";
import { Cell, Pie, PieChart, ResponsiveContainer, Tooltip } from "recharts";

export const NodeStats: FC = () => {
  const {
    state: {
      aggregatedData,
      graph: { currentNode },
      topography,
    },
  } = useSimContext();

  const currentNodeStats = useMemo(() => {
    return currentNode ? aggregatedData.nodes.get(currentNode) : undefined;
  }, [currentNode, aggregatedData.nodes]);

  const getCounts = (type: EMessageType) => {
    const sent = currentNodeStats?.sent?.get(type)?.bytes ?? 0;
    const received = currentNodeStats?.received?.get(type)?.bytes ?? 0;
    return { sent, received };
  };

  const getPeerLatencies = useMemo(() => {
    if (!currentNode || !topography.links) return [];

    const peers: { peerId: string; latencyMs: number | null }[] = [];

    // Find all links involving the current node
    topography.links.forEach((link) => {
      if (link.source === currentNode || link.target === currentNode) {
        const peerId = link.source === currentNode ? link.target : link.source;
        peers.push({
          peerId,
          latencyMs: link.latencyMs || null,
        });
      }
    });

    return peers.sort((a, b) => a.peerId.localeCompare(b.peerId));
  }, [currentNode, topography.links]);

  const data = [
    { name: "Transactions", ...getCounts(EMessageType.TX), color: "#26de81" },
    { name: "Input Blocks", ...getCounts(EMessageType.IB), color: "#2bcbba" },
    { name: "Endorser Blocks", ...getCounts(EMessageType.EB), color: "#4b7bec" },
    { name: "Votes", ...getCounts(EMessageType.Votes), color: "#2d98da" },
    { name: "Blocks", ...getCounts(EMessageType.RB), color: "#fc5c65" },
  ];

  return (
    <div className="border-2 border-gray-200 rounded-sm p-4 z-30 bg-white/80 backdrop-blur-xs min-w-[220px] block">
      <h2 className="flex items-center justify-between gap-4 font-bold uppercase mb-2">
        Node Stats <span>{currentNode}</span>
      </h2>

      {/* Peer Latencies Section */}
      {getPeerLatencies.length > 0 && (
        <div className="mb-4">
          <h3 className="font-semibold text-sm mb-2">Peer Latencies</h3>
          <div className="max-h-32 overflow-y-auto text-xs">
            {getPeerLatencies.map(({ peerId, latencyMs }) => (
              <div
                key={peerId}
                className="flex justify-between items-center py-1"
              >
                <span className="text-gray-700">{peerId}:</span>
                <span className="font-mono">
                  {latencyMs !== null ? `${latencyMs}ms` : "N/A"}
                </span>
              </div>
            ))}
          </div>
        </div>
      )}

      {currentNodeStats && (
        <div className="w-full h-full">
          <h2 className="text-center">
            Bytes Sent: {printBytes(currentNodeStats.bytesSent)}
          </h2>
          <ResponsiveContainer width="100%" height={200}>
            <PieChart>
              <Pie dataKey="sent" data={data}>
                {data.map((d, index) => (
                  <Cell key={index} fill={d.color} />
                ))}
              </Pie>
              <Tooltip formatter={printBytes} />
            </PieChart>
          </ResponsiveContainer>
          <h2 className="text-center">
            Bytes Received: {printBytes(currentNodeStats.bytesReceived)}
          </h2>
          <ResponsiveContainer width="100%" height={200}>
            <PieChart>
              <Pie dataKey="received" data={data}>
                {data.map((d, index) => (
                  <Cell key={index} fill={d.color} />
                ))}
              </Pie>
              <Tooltip formatter={printBytes} />
            </PieChart>
          </ResponsiveContainer>
        </div>
      )}
    </div>
  );
};
