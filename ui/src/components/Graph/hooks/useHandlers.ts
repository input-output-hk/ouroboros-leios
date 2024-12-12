import {
  defaultAggregatedData,
  useGraphContext,
} from "@/contexts/GraphContext/context";
import { useCallback } from "react";


export const useHandlers = () => {
  const {
    state: {
      aggregatedData,
      canvasRef,
      canvasOffsetX,
      canvasOffsetY,
      canvasScale,
      currentNode,
      maxTime,
      topography,
    },
    dispatch,
  } = useGraphContext();

  const drawTopography = useCallback(() => {
    const canvas = canvasRef.current;
    const context = canvas?.getContext("2d");
    if (!context || !canvas) {
      return;
    }

    // Set canvas dimensions
    const width = canvas.parentElement?.getBoundingClientRect().width || 1024;
    const height = canvas.parentElement?.getBoundingClientRect().height || 800;
    canvas.width = width;
    canvas.height = height;

    // Clear the canvas
    context.clearRect(0, 0, width, height);
    context.save();

    // Apply translation and scaling
    context.translate(canvasOffsetX, canvasOffsetY);
    context.scale(canvasScale, canvasScale);

    // Draw the links
    topography.links.forEach((link) => {
      const nodeStart = topography.nodes.get(link.source);
      const nodeEnd = topography.nodes.get(link.target);
      if (!nodeStart || !nodeEnd) {
        return;
      }

      context.beginPath();
      context.moveTo(nodeStart.fx, nodeStart.fy);
      context.lineTo(nodeEnd.fx, nodeEnd.fy);
      context.strokeStyle = "#ddd";
      context.lineWidth = 0.2;
      context.stroke();
    });

    // Draw the nodes
    topography.nodes.forEach((node) => {
      context.beginPath();
      context.arc(node.fx, node.fy, 1, 0, 2 * Math.PI);
      context.fillStyle = node.data.stake ? "green" : "blue";
      context.stroke();
      context.lineWidth = 1;
      
      const hasData = aggregatedData.nodes.has(node.id.toString());
      if (hasData) {
        context.strokeStyle = "red";
      } else {
        context.strokeStyle = "black";
      }

      if (currentNode === node.id.toString()) {
        console.log(node.id, hasData, aggregatedData.nodes.get(node.id.toString()))
        context.fillStyle = "red";
      }


      context.fill();
    });

    context.restore();
  }, [
    maxTime,
    topography.nodes,
    topography.links,
    currentNode,
    canvasOffsetX,
    canvasOffsetY,
    canvasScale
  ]);

  const handleResetSim = useCallback(() => {
    dispatch({
      type: "BATCH_UPDATE",
      payload: {
        currentNode: undefined,
        aggregatedData: defaultAggregatedData,
      },
    });

    drawTopography();
  }, []);

  return {
    handleResetSim,
    drawTopography,
  };
};
