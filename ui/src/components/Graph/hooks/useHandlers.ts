import { useSimContext } from "@/contexts/SimContext/context";
import { EMessageType } from "@/contexts/SimContext/types";
import { ELinkColor, EMessageColor, ENodeColor } from "@/utils/colors";
import { useCallback } from "react";

export const useHandlers = () => {
  const {
    state: {
      aggregatedData,
      currentTime,
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

  const ACTIVITY_TIMEOUT = 1.0; // seconds after which node color resets

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
      context.strokeStyle = ELinkColor.LINK_DEFAULT;

      if (link.source === currentNode || link.target === currentNode) {
        context.strokeStyle = ELinkColor.LINK_SELECTED;
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
        context.fillStyle = ENodeColor.SELECTED;
      } else {
        // Color based on last activity
        const nodeStats = aggregatedData.nodes.get(node.id.toString());
        const lastActivity = nodeStats?.lastActivity;

        // Check if activity is recent (within timeout)
        const activityIsRecent =
          lastActivity && currentTime - lastActivity.time <= ACTIVITY_TIMEOUT;

        if (activityIsRecent) {
          if (lastActivity.type === EMessageType.EB) {
            context.fillStyle = EMessageColor.EB;
          } else if (lastActivity.type === EMessageType.RB) {
            context.fillStyle = EMessageColor.RB;
          } else {
            context.fillStyle = node.data.stake
              ? ENodeColor.STAKE_NODE
              : ENodeColor.SELECTED;
          }
        } else if (!node.data.stake) {
          context.fillStyle = ENodeColor.INACTIVE;
        } else {
          context.fillStyle = ENodeColor.STAKE_NODE;
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

      // Draw colored rectangle based on message type (consistent with pie chart colors)
      const rectSize = Math.min((0.8 / canvasScale) * 6, 0.8);

      switch (message.type) {
        case EMessageType.TX:
          context.fillStyle = EMessageColor.TX;
          break;
        case EMessageType.EB:
          context.fillStyle = EMessageColor.EB;
          break;
        case EMessageType.Votes:
          context.fillStyle = EMessageColor.VOTES;
          break;
        case EMessageType.RB:
          context.fillStyle = EMessageColor.RB;
          break;
      }
      context.fillRect(x - rectSize / 2, y - rectSize / 2, rectSize, rectSize);
    });

    context.restore();
  }, [
    aggregatedData,
    currentTime,
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
