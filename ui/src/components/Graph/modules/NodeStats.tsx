import { useSimContext } from "@/contexts/SimContext/context";
import { printBytes } from "@/utils";
import { FC, useMemo, useRef } from "react";
import { Cell, Pie, PieChart, ResponsiveContainer, Tooltip } from "recharts";

interface ILabelProps {
}

export const NodeStats: FC = () => {
  const {
    state: {
      aggregatedData,
      topography,
      graph: {
        currentNode,
        canvasOffsetX,
        canvasOffsetY,
        canvasScale,
      }
    },
  } = useSimContext();
  const ref = useRef<HTMLDivElement>(null);
  const currentNodeStats = useMemo(() => {
    return currentNode ? aggregatedData.nodes.get(currentNode) : undefined;
  }, [currentNode, aggregatedData.nodes]);

  const currentNodeData = useMemo(
    () => currentNode ? topography.nodes.get(currentNode) : undefined,
    [currentNode, topography],
  );
  const { left, top } = useMemo(() => {
    const margin = 10;
    const elementRect = ref.current?.getBoundingClientRect();

    if (!elementRect) {
      return { left: 0, top: 0 };
    }

    const fx = currentNodeData?.fx ?? 0;
    const fy = currentNodeData?.fy ?? 0;

    // Convert node position to canvas pixel space
    const nodeCanvasX = fx * canvasScale + canvasOffsetX;
    const nodeCanvasY = fy * canvasScale + canvasOffsetY;

    // Start by placing the box with bottom-left corner at the node's position
    let calculatedLeft = nodeCanvasX + margin;
    let calculatedTop = nodeCanvasY - margin - elementRect.height;

    // If the box goes off the top of the screen, place it below the node
    if (calculatedTop < 0) {
      calculatedTop = nodeCanvasY - margin;
    }

    // If the box goes off the right side of the screen, place it to the left of the node
    if (calculatedLeft + elementRect.width > screen.width) {
      calculatedLeft = nodeCanvasX - elementRect.width - margin;
    } else if (calculatedLeft < 0) {
      // If it goes off the left side, adjust to the right again
      calculatedLeft = nodeCanvasX - margin;
    }

    return {
      left: calculatedLeft,
      top: calculatedTop,
    };
  }, [currentNodeData, canvasScale, canvasOffsetX, canvasOffsetY]);

  const getCounts = (type: string) => {
    const sent = currentNodeStats?.sent?.[type]?.bytes ?? 0;
    const received = currentNodeStats?.received?.[type]?.bytes ?? 0;
    return { sent, received }
  }

  const data = [
    { name: "Transactions", ...getCounts("tx"), color: '#26de81' },
    { name: "Input Blocks", ...getCounts("ib"), color: '#2bcbba' },
    { name: "Endorser Blocks", ...getCounts("eb"), color: '#4b7bec' },
    { name: "Votes", ...getCounts("votes"), color: '#2d98da' },
    { name: "Blocks", ...getCounts("pb"), color: '#fc5c65' },
  ]

  return (
    <div
      ref={ref}
      className={`border-2 border-gray-200 rounded-sm p-4 absolute z-30 bg-white/80 backdrop-blur-xs min-w-[220px] ${Boolean(currentNodeData && currentNodeStats) ? "block" : "hidden"}`}
      style={{
        left,
        top
      }}
    >
      <h2 className="flex items-center justify-between gap-4 font-bold uppercase mb-2">
        Node Stats <span>{currentNode}</span>
      </h2>
      {currentNodeStats && (
        <div className="w-full h-full">
          <h2 className="text-center">Bytes Sent: {printBytes(currentNodeStats.bytesSent)}</h2>
          <ResponsiveContainer width="100%" height={200}>
            <PieChart>
              <Pie dataKey="sent" data={data}>
                {data.map((d, index) => <Cell key={index} fill={d.color} />)}
              </Pie>
              <Tooltip formatter={printBytes} />
            </PieChart>
          </ResponsiveContainer>
          <h2 className="text-center">Bytes Received: {printBytes(currentNodeStats.bytesReceived)}</h2>
          <ResponsiveContainer width="100%" height={200}>
            <PieChart>
              <Pie dataKey="received" data={data}>
                {data.map((d, index) => <Cell key={index} fill={d.color} />)}
              </Pie>
              <Tooltip formatter={printBytes} />
            </PieChart>
          </ResponsiveContainer>
        </div>
      )}
    </div>
  );
};
