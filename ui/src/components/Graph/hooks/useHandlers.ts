import { useSimContext } from "@/contexts/SimContext/context";
import { useCallback } from "react";

export const useHandlers = () => {
  const {
    state: {
      aggregatedData,
      graph: {
        canvasOffsetX,
        canvasOffsetY,
        canvasRef,
        canvasScale,
        currentNode,
      },
      maxTime,
      topography,
    },
  } = useSimContext();

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

      if (link.source === currentNode || link.target === currentNode) {
        context.strokeStyle = "black";
      }

      context.lineWidth = Math.min((0.2 / canvasScale) * 6, 0.2);
      context.stroke();
    });

    // Draw the nodes
    topography.nodes.forEach((node) => {
      context.beginPath();
      context.arc(
        node.fx,
        node.fy,
        Math.min((1 / canvasScale) * 6, 1),
        0,
        2 * Math.PI,
      );
      context.fillStyle = node.data.stake ? "#DC53DE" : "blue";
      context.stroke();
      context.lineWidth = Math.min((0.5 / canvasScale) * 6, 0.5);

      if (aggregatedData.lastNodesUpdated.includes(node.id.toString())) {
        context.strokeStyle = "red";
      } else {
        context.strokeStyle = "black";
      }

      if (currentNode === node.id.toString()) {
        context.fillStyle = "blue";
      } else {
        // Color based on last activity
        const nodeStats = aggregatedData.nodes.get(node.id.toString());
        const lastActivity = nodeStats?.lastActivity;

        if (lastActivity) {
          if (lastActivity.type === "eb") {
            context.fillStyle = "#9333ea"; // Purple for EB-related activity
          } else if (lastActivity.type === "rb") {
            context.fillStyle = "#87ceeb"; // Light blue for RB-related activity
          } else {
            context.fillStyle = node.data.stake ? "#DC53DE" : "blue"; // Default colors
          }
        } else if (!node.data.stake) {
          context.fillStyle = "gray";
        } else {
          context.fillStyle = "#DC53DE"; // Stake node default
        }
      }

      context.fill();
    });

    // Draw message animations
    aggregatedData.messages.forEach((message) => {
      const senderNode = topography.nodes.get(message.sender);
      const recipientNode = topography.nodes.get(message.recipient);

      if (!senderNode || !recipientNode) {
        return;
      }

      // Calculate position along the edge based on progress (0-1)
      const x =
        senderNode.fx + (recipientNode.fx - senderNode.fx) * message.progress;
      const y =
        senderNode.fy + (recipientNode.fy - senderNode.fy) * message.progress;

      // Draw purple rectangle for EB messages
      const rectSize = Math.min((0.8 / canvasScale) * 6, 0.8);
      context.fillStyle = "#9333ea"; // Purple color
      context.fillRect(x - rectSize / 2, y - rectSize / 2, rectSize, rectSize);

      // Add a slight border for visibility
      context.strokeStyle = "#7c3aed";
      context.lineWidth = Math.min((0.1 / canvasScale) * 6, 0.1);
      context.strokeRect(
        x - rectSize / 2,
        y - rectSize / 2,
        rectSize,
        rectSize,
      );
    });

    context.restore();
  }, [
    aggregatedData,
    maxTime,
    topography.nodes,
    topography.links,
    currentNode,
    canvasOffsetX,
    canvasOffsetY,
    canvasScale,
  ]);

  return {
    drawTopography,
  };
};
