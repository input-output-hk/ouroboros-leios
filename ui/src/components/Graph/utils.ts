import { ITransformedNodeMap } from "@/components/Sim/types";

export const isWithinRange = (
  elapsedTimestamp: number,
  targetTimestamp: number,
  rangeInMilliseconds: number,
): boolean => {
  const difference = elapsedTimestamp - targetTimestamp;
  return difference >= 0 && difference <= rangeInMilliseconds;
};

export const getOffsetCoordinates = (
  topography: ITransformedNodeMap,
  width: number,
  height: number,
  scale: number,
) => {
  let offsetX = 0,
    offsetY = 0;

  // Calculate the bounds
  const coordinates: { xValues: number[]; yValues: number[] } = {
    xValues: [],
    yValues: [],
  };
  for (const [_, { fx, fy }] of topography.nodes) {
    coordinates.xValues.push(fx);
    coordinates.yValues.push(fy);
  }
  const minX = Math.min(...coordinates.xValues);
  const maxX = Math.max(...coordinates.xValues);
  const minY = Math.min(...coordinates.yValues);
  const maxY = Math.max(...coordinates.yValues);

  const pathWidth = maxX - minX;
  const pathHeight = maxY - minY;

  // Compute the canvas center
  const canvasCenterX = width / 2;
  const canvasCenterY = height / 2;

  // Calculate the offset to center the path
  offsetX = canvasCenterX - (minX + pathWidth / 2) * scale;
  offsetY = canvasCenterY - (minY + pathHeight / 2) * scale;

  return {
    offsetX,
    offsetY,
  };
};

export type ClickTarget =
  | { kind: "node"; id: string }
  | { kind: "edge"; id: string }
  | { kind: "background" };

export const findClickTarget = (
  clickX: number,
  clickY: number,
  topography: ITransformedNodeMap,
  threshold: number,
  offsetX: number,
  offsetY: number,
  scale: number,
): ClickTarget => {
  const adjustedX = (clickX - offsetX) / scale;
  const adjustedY = (clickY - offsetY) / scale;

  // Find closest node
  let closestNodeDist = Infinity;
  let closestNode: string | undefined;
  for (const [, { fx, fy, id }] of topography.nodes) {
    const dist = Math.sqrt((fx - adjustedX) ** 2 + (fy - adjustedY) ** 2);
    if (dist < closestNodeDist) {
      closestNodeDist = dist;
      closestNode = id.toString();
    }
  }

  // Find closest edge (by perpendicular distance to line segment)
  let closestEdgeDist = Infinity;
  let closestEdge: string | undefined;
  topography.links.forEach((link, key) => {
    const a = topography.nodes.get(link.source);
    const b = topography.nodes.get(link.target);
    if (!a || !b) return;

    const dx = b.fx - a.fx;
    const dy = b.fy - a.fy;
    const lenSq = dx * dx + dy * dy;
    if (lenSq === 0) return;

    const t = Math.max(
      0,
      Math.min(1, ((adjustedX - a.fx) * dx + (adjustedY - a.fy) * dy) / lenSq),
    );
    const dist = Math.sqrt(
      (adjustedX - (a.fx + t * dx)) ** 2 + (adjustedY - (a.fy + t * dy)) ** 2,
    );

    if (dist < closestEdgeDist) {
      closestEdgeDist = dist;
      closestEdge = key;
    }
  });

  // Pick whichever is closer, as long as it's within threshold
  if (closestNodeDist <= threshold && closestNodeDist <= closestEdgeDist) {
    return { kind: "node", id: closestNode! };
  }
  if (closestEdgeDist <= threshold && closestEdge) {
    return { kind: "edge", id: closestEdge };
  }
  if (closestNodeDist <= threshold && closestNode) {
    return { kind: "node", id: closestNode };
  }
  return { kind: "background" };
};
