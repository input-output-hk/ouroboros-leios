import { useSimContext } from "@/contexts/SimContext/context";
import { printBytes } from "@/utils";
import { FC, useMemo } from "react";
import { Cell, Pie, PieChart, ResponsiveContainer, Tooltip } from "recharts";

export const NodeStats: FC = () => {
  const {
    state: {
      aggregatedData,
      graph: { currentNode },
    },
  } = useSimContext();

  // FIXME: NodeStats are broken - aggregatedData.nodes is not being populated correctly
  // with the new timeline-based architecture. Need to implement proper aggregation
  // based on currentTime and timeline events.
  const currentNodeStats = useMemo(() => {
    return currentNode ? aggregatedData.nodes.get(currentNode) : undefined;
  }, [currentNode, aggregatedData.nodes]);

  const getCounts = (type: string) => {
    const sent = currentNodeStats?.sent?.[type]?.bytes ?? 0;
    const received = currentNodeStats?.received?.[type]?.bytes ?? 0;
    return { sent, received };
  };

  const data = [
    { name: "Transactions", ...getCounts("tx"), color: "#26de81" },
    { name: "Input Blocks", ...getCounts("ib"), color: "#2bcbba" },
    { name: "Endorser Blocks", ...getCounts("eb"), color: "#4b7bec" },
    { name: "Votes", ...getCounts("votes"), color: "#2d98da" },
    { name: "Blocks", ...getCounts("pb"), color: "#fc5c65" },
  ];

  return (
    <div className="border-2 border-gray-200 rounded-sm p-4 z-30 bg-white/80 backdrop-blur-xs min-w-[220px] block">
      <h2 className="flex items-center justify-between gap-4 font-bold uppercase mb-2">
        Node Stats <span>{currentNode}</span>
      </h2>
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
