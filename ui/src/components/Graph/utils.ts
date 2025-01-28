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
  scale: number
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

export const isClickOnNode = (
  clickX: number,
  clickY: number,
  topography: ITransformedNodeMap,
  threshold: number = 10,
  offsetX: number,
  offsetY: number,
  scale: number
): { node: string | undefined, clicked: boolean } => {
  let node: string | undefined;
  let clicked = false;

  // Adjust the click coordinates based on the offset
  const adjustedClickX = (clickX - offsetX) / scale;
  const adjustedClickY = (clickY - offsetY) / scale;

  // Iterate through nodes to find if the click is within threshold
  for (const [, { fx, fy, id }] of topography.nodes) {
    const xDifference = Math.abs(fx - adjustedClickX);
    const yDifference = Math.abs(fy - adjustedClickY);

    if (xDifference <= threshold && yDifference <= threshold) {
      clicked = true;
      node = id.toString();
      break;
    }
  }

  return { node, clicked };
};
