import { useGraphContext } from "@/contexts/GraphContext/context";
import { FC, useMemo, useRef } from "react";

export const NodeStats: FC = () => {
  const {
    state: {
      aggregatedData,
      currentNode,
      topography,
      canvasOffsetX,
      canvasOffsetY,
      canvasScale,
    },
  } = useGraphContext();
  const ref = useRef<HTMLDivElement>(null);
  const currentNodeStats = useMemo(() => {
    return currentNode ? aggregatedData.nodes.get(currentNode) : undefined;
  }, [currentNode, aggregatedData.nodes]);

  const currentNodeData = useMemo(
    () => topography.nodes.get(Number(currentNode)),
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
  
  return (
    <div
      ref={ref}
      className={`border-2 border-gray-200 rounded p-4 absolute z-30 bg-white/80 backdrop-blur-sm min-w-[220px] ${Boolean(currentNodeData && currentNodeStats) ? "block" : "hidden"}`}
      style={{
        left,
        top
      }}
    >
      <h2 className="flex items-center justify-between gap-4 font-bold uppercase mb-2">
        Node Stats <span>ID: #{currentNode}</span>
      </h2>
      {currentNodeStats && (
        <>
          <h4 className="flex items-center justify-between gap-4">Tx Generated: <span>{currentNodeStats?.txGenerated}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Tx Sent: <span>{currentNodeStats?.txSent}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Tx Received: <span>{currentNodeStats?.txReceived}</span></h4>
          <h4 className="flex items-center justify-between gap-4">EB Generated: <span>{currentNodeStats?.ebGenerated}</span></h4>
          <h4 className="flex items-center justify-between gap-4">EB Sent: <span>{currentNodeStats?.ebSent}</span></h4>
          <h4 className="flex items-center justify-between gap-4">EB Received: <span>{currentNodeStats?.ebReceived}</span></h4>
          <h4 className="flex items-center justify-between gap-4">IB Generated: <span>{currentNodeStats?.ibGenerated}</span></h4>
          <h4 className="flex items-center justify-between gap-4">IB Sent: <span>{currentNodeStats?.ibSent}</span></h4>
          <h4 className="flex items-center justify-between gap-4">IB Received: <span>{currentNodeStats?.ibReceived}</span></h4>
          <h4 className="flex items-center justify-between gap-4">PB Generated: <span>{currentNodeStats?.pbGenerated}</span></h4>
          <h4 className="flex items-center justify-between gap-4">PB Sent: <span>{currentNodeStats?.pbSent}</span></h4>
          <h4 className="flex items-center justify-between gap-4">PB Received: <span>{currentNodeStats?.pbReceived}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Votes Generated: <span>{currentNodeStats?.votesGenerated}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Votes Sent: <span>{currentNodeStats?.votesSent}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Votes Received: <span>{currentNodeStats?.votesReceived}</span></h4>
        </>
      )}
    </div>
  );
};
