import { useSimContext } from "@/contexts/SimContext/context";
import { EMessageType, MercatorParams } from "@/contexts/SimContext/types";
import { ELinkColor, EMessageColor, ENodeColor } from "@/utils/colors";
import { mercatorProject } from "@/hooks/useGraphLayout";
import { useCallback } from "react";

// Import helper function from timelineAggregation
const getHighestPriorityMessageType = (counts: {
  [key in EMessageType]: number;
}): EMessageType | null => {
  const MESSAGE_PRIORITY_ORDER = [
    EMessageType.RB, // Highest priority
    EMessageType.Announcement,
    EMessageType.EB,
    EMessageType.Txs, // EB txs, pulled once the EB is known
    EMessageType.Votes, // Lowest priority
  ];

  for (const messageType of MESSAGE_PRIORITY_ORDER) {
    if (counts[messageType] > 0) {
      return messageType;
    }
  }
  return null;
};

function drawMapBackground(
  ctx: CanvasRenderingContext2D,
  geoJson: GeoJSON.FeatureCollection,
  params: MercatorParams,
  canvasScale: number,
) {
  ctx.strokeStyle = "#ccc";
  ctx.fillStyle = "#e8f5e9";
  ctx.lineWidth = Math.min((0.2 / canvasScale) * 6, 0.2);

  for (const feature of geoJson.features) {
    const geometry = feature.geometry;
    if (!geometry) continue;

    const rings: number[][][] =
      geometry.type === "Polygon"
        ? (geometry as GeoJSON.Polygon).coordinates
        : geometry.type === "MultiPolygon"
          ? (geometry as GeoJSON.MultiPolygon).coordinates.flat()
          : [];

    for (const ring of rings) {
      ctx.beginPath();
      for (let i = 0; i < ring.length; i++) {
        const [lon, lat] = ring[i];
        const { x, y } = mercatorProject(lat, lon, params);
        if (i === 0) {
          ctx.moveTo(x, y);
        } else {
          ctx.lineTo(x, y);
        }
      }
      ctx.closePath();
      ctx.fill();
      ctx.stroke();
    }
  }
}

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
        currentEdge,
      },
      maxTime,
      topography,
      layoutMode,
      mercatorParams,
      mapGeoJson,
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

    // Draw world map background when in Mercator mode
    if (layoutMode === "mercator" && mercatorParams && mapGeoJson) {
      drawMapBackground(context, mapGeoJson, mercatorParams, canvasScale);
    }

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

      // Set edge color based on selection, highest priority message type, or default
      if (edgeKey === currentEdge) {
        context.strokeStyle = ELinkColor.LINK_SELECTED;
        context.lineWidth = Math.min((0.5 / canvasScale) * 6, 0.5);
      } else if (link.source === currentNode || link.target === currentNode) {
        context.strokeStyle = ELinkColor.LINK_SELECTED;
      } else if (edgeState) {
        // Get highest priority message type currently traveling
        const highestPriorityType = getHighestPriorityMessageType(
          edgeState.activeCounts,
        );
        if (highestPriorityType) {
          switch (highestPriorityType) {
            case EMessageType.Txs:
              context.strokeStyle = EMessageColor.TXS;
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
            case EMessageType.Announcement:
              context.strokeStyle = EMessageColor.ANNOUNCEMENT;
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
      // Dotted until a message has crossed this edge (in either direction),
      // solid thereafter — so links that are never used stay visibly dashed.
      if (!aggregatedData.traversedEdges.has(edgeKey)) {
        const dash = context.lineWidth * 3;
        context.setLineDash([dash, dash]);
      }
      context.stroke();
      context.setLineDash([]);
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
            case EMessageType.Txs:
              context.fillStyle = EMessageColor.TXS;
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
            case EMessageType.Announcement:
              context.fillStyle = EMessageColor.ANNOUNCEMENT;
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

      switch (message.type) {
        case EMessageType.Txs:
          context.fillStyle = EMessageColor.TXS;
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
        case EMessageType.Announcement:
          context.fillStyle = EMessageColor.ANNOUNCEMENT;
          break;
      }

      // Votes and announcements: small fixed-size circles (no bandwidth
      // scaling) — both are lightweight control messages, not bulk data.
      if (
        message.type === EMessageType.Votes ||
        message.type === EMessageType.Announcement
      ) {
        const radius = Math.min((0.4 / canvasScale) * 6, 0.4);
        context.beginPath();
        context.arc(x, y, radius, 0, 2 * Math.PI);
        context.fill();
        return;
      }

      // Other message types: draw as oriented rectangles scaled by bandwidth
      const rectHeight = Math.min((0.8 / canvasScale) * 6, 0.8);

      // Bulk messages are drawn as the span of wire they occupy, between a
      // leading and a trailing edge rather than as one sliding block:
      //
      //   lead  leaves the sender at sentTime, arrives one latency later
      //   tail  leaves once the last byte is out (sizeBytes / bandwidth),
      //         and likewise arrives a latency after that
      //
      // So the frontier crosses first, the span behind it grows while the
      // sender is still transmitting -- a big message simply loads the whole
      // link -- and the tail then follows and drains it. A message far larger
      // than its pipe saturates the edge for the duration, which is what
      // 345ms of transmission against 10ms of flight actually means.
      const linkIds = [message.sender, message.recipient].sort();
      const linkKey = `${linkIds[0]}|${linkIds[1]}`;
      const link = topography.links.get(linkKey);
      const bandwidth = link?.bandwidthBytesPerSecond;

      const dx = recipientNode.fx - senderNode.fx;
      const dy = recipientNode.fy - senderNode.fy;
      const edgeLength = Math.sqrt(dx * dx + dy * dy);
      const angle = Math.atan2(dy, dx);

      // The measurement decides the duration; the configured values only
      // decide the shape. `progress` already spans the observed sent -> received
      // interval, so the span is expressed as fractions *of that interval*:
      // configured latency and bandwidth say how much of it is the frontier
      // crossing versus the sender still pushing bytes, and nothing more.
      //
      // Consequences worth having: the span always starts empty and finishes
      // drained exactly when the observed transfer ends, so a model that
      // disagrees with the trace cannot leave a marker parked at the recipient
      // or make one vanish mid-transfer. Where the link has no configured
      // bandwidth, or the message no size, it degenerates to pure propagation
      // -- a marker riding the frontier, which is the honest depiction of
      // "we know when it left and when it landed, nothing more".
      const clamp01 = (v: number) => (v < 0 ? 0 : v > 1 ? 1 : v);
      const u = clamp01(message.progress);

      const latencySeconds = link?.latencyMs ? link.latencyMs / 1000 : 0;
      const transmissionSeconds =
        message.sizeBytes > 0 && bandwidth && bandwidth > 0
          ? message.sizeBytes / bandwidth
          : 0;
      const modelSeconds = latencySeconds + transmissionSeconds;

      // Shares of the observed interval, not absolute times.
      const latencyShare = modelSeconds > 0 ? latencySeconds / modelSeconds : 1;
      const transmissionShare =
        modelSeconds > 0 ? transmissionSeconds / modelSeconds : 0;

      const lead = latencyShare > 0 ? clamp01(u / latencyShare) : 1;
      const tail =
        latencyShare > 0
          ? clamp01((u - transmissionShare) / latencyShare)
          : clamp01(u);

      // Keep a minimum extent so a message far smaller than its pipe stays
      // visible as a marker at the frontier instead of a zero-width sliver.
      const spanLength = Math.max(rectHeight, (lead - tail) * edgeLength);
      const leadDistance = lead * edgeLength;
      const startDistance = Math.max(0, leadDistance - spanLength);

      context.save();
      context.translate(senderNode.fx, senderNode.fy);
      context.rotate(angle);
      context.fillRect(
        startDistance,
        -rectHeight / 2,
        leadDistance - startDistance,
        rectHeight,
      );
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
    currentEdge,
    canvasOffsetX,
    canvasOffsetY,
    canvasScale,
    layoutMode,
    mercatorParams,
    mapGeoJson,
  ]);

  return {
    drawTopography,
  };
};
