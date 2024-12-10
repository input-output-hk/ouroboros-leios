import {
  ISimulationAggregatedData,
  ISimulationAggregatedDataState,
} from "@/contexts/GraphContext/types";
import { ITransformedNodeMap } from "./types";

export const CANVAS_SCALE = 4;

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
  offsetX = canvasCenterX - (minX + pathWidth / 2) * CANVAS_SCALE;
  offsetY = canvasCenterY - (minY + pathHeight / 2) * CANVAS_SCALE;

  return {
    offsetX,
    offsetY,
  };
};

export const isClickOnNode = (
  clickX: number,
  clickY: number,
  topography: ITransformedNodeMap,
  width: number,
  height: number,
  threshold: number = 10,
): { node: string | undefined, clicked: boolean } => {
  let node: string | undefined;
  let clicked = false;

  // Get the offsets
  const { offsetX, offsetY } = getOffsetCoordinates(topography, width, height);

  // Adjust the click coordinates based on the offset
  const adjustedClickX = (clickX - offsetX) / CANVAS_SCALE;
  const adjustedClickY = (clickY - offsetY) / CANVAS_SCALE;

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

export const incrementNodeAggregationData = (
  aggregationNodeDataRef: ISimulationAggregatedDataState["nodes"],
  id: string,
  key: keyof ISimulationAggregatedData,
) => {
  const matchingNode = aggregationNodeDataRef.get(id);
  aggregationNodeDataRef.set(id, {
    ebGenerated: 0,
    ebReceived: 0,
    ebSent: 0,
    ibGenerated: 0,
    ibReceived: 0,
    ibSent: 0,
    pbGenerated: 0,
    pbReceived: 0,
    pbSent: 0,
    txGenerated: 0,
    txPerSecond: 0,
    txPropagations: 0,
    txReceived: 0,
    txSent: 0,
    ...matchingNode,
    [key]: (matchingNode?.[key] || 0) + 1,
  });
};
