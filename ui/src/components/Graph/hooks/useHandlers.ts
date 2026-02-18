import { useSimContext } from "@/contexts/SimContext/context";
import { EMessageType } from "@/contexts/SimContext/types";
import { ELinkColor, EMessageColor, ENodeColor } from "@/utils/colors";
import { useCallback } from "react";

// Import helper function from timelineAggregation
const getHighestPriorityMessageType = (counts: {
  [key in EMessageType]: number;
}): EMessageType | null => {
  const MESSAGE_PRIORITY_ORDER = [
    EMessageType.RB, // Highest priority
    EMessageType.EB,
    EMessageType.Votes,
    EMessageType.TX, // Lowest priority
  ];

  for (const messageType of MESSAGE_PRIORITY_ORDER) {
    if (counts[messageType] > 0) {
      return messageType;
    }
  }
  return null;
};

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

      // Create edge key for lookup (consistent with aggregation logic)
      const edgeIds = [link.source, link.target].sort();
      const edgeKey = `${edgeIds[0]}|${edgeIds[1]}`;
      const edgeState = aggregatedData.edges.get(edgeKey);

      // Set edge color based on highest priority message type or default
      if (link.source === currentNode || link.target === currentNode) {
        context.strokeStyle = ELinkColor.LINK_SELECTED;
      } else if (edgeState) {
        // Get highest priority message type currently traveling
        const highestPriorityType = getHighestPriorityMessageType(
          edgeState.activeCounts,
        );
        if (highestPriorityType) {
          switch (highestPriorityType) {
            case EMessageType.TX:
              context.strokeStyle = EMessageColor.TX;
              break;
            case EMessageType.EB:
              context.strokeStyle = EMessageColor.EB;
              break;
            case EMessageType.RB:
              context.strokeStyle = EMessageColor.RB;
              break;
            case EMessageType.Votes:
              context.strokeStyle = EMessageColor.VOTES;
              break;
            default:
              context.strokeStyle = ELinkColor.LINK_DEFAULT;
          }
        } else {
          context.strokeStyle = ELinkColor.LINK_DEFAULT;
        }
      } else {
        context.strokeStyle = ELinkColor.LINK_DEFAULT;
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
      context.lineWidth = Math.min((0.5 / canvasScale) * 6, 0.5);
      context.strokeStyle = "black";
      context.stroke();
      context.fillStyle = node.data.stake ? "#DC53DE" : "blue";

      if (currentNode === node.id.toString()) {
        context.fillStyle = ENodeColor.SELECTED;
      } else {
        // Color based on priority-based node activity
        const nodeActivity = aggregatedData.nodeActivity.get(
          node.id.toString(),
        );
        const highestPriorityType = nodeActivity
          ? getHighestPriorityMessageType(nodeActivity.activeCounts)
          : null;

        if (highestPriorityType) {
          // Node has active messages - color by highest priority
          switch (highestPriorityType) {
            case EMessageType.TX:
              context.fillStyle = EMessageColor.TX;
              break;
            case EMessageType.EB:
              context.fillStyle = EMessageColor.EB;
              break;
            case EMessageType.RB:
              context.fillStyle = EMessageColor.RB;
              break;
            case EMessageType.Votes:
              context.fillStyle = EMessageColor.VOTES;
              break;
            default:
              context.fillStyle = node.data.stake
                ? ENodeColor.STAKE_NODE
                : ENodeColor.INACTIVE;
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
      const rectHeight = Math.min((0.8 / canvasScale) * 6, 0.8);

      // Scale length by transmission time relative to travel time:
      // transmissionTime = sizeBytes / bandwidth, fraction = transmissionTime / travelTime
      const linkIds = [message.sender, message.recipient].sort();
      const linkKey = `${linkIds[0]}|${linkIds[1]}`;
      const link = topography.links.get(linkKey);
      const bandwidth = link?.bandwidthBytesPerSecond;
      const travelTime = message.receivedTime - message.sentTime;

      // Visual length as fraction of edge length
      const dx = recipientNode.fx - senderNode.fx;
      const dy = recipientNode.fy - senderNode.fy;
      const edgeLength = Math.sqrt(dx * dx + dy * dy);

      let rectLength = rectHeight;
      if (message.sizeBytes > 0 && bandwidth && bandwidth > 0 && travelTime > 0) {
        const transmissionFraction = message.sizeBytes / bandwidth / travelTime;
        rectLength = Math.max(rectHeight, edgeLength * transmissionFraction);
      }

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

      // Orient rectangle along travel direction
      const angle = Math.atan2(dy, dx);
      context.save();
      context.translate(x, y);
      context.rotate(angle);
      context.fillRect(-rectLength / 2, -rectHeight / 2, rectLength, rectHeight);
      context.restore();
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
