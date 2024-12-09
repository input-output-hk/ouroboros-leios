import {
  defaultAggregatedData,
  useGraphContext,
} from "@/contexts/GraphContext/context";
import { ESpeedOptions } from "@/contexts/GraphContext/types";
import { useCallback } from "react";

import { CANVAS_SCALE, getOffsetCoordinates } from "../utils";
import { useStreamMessagesHandler } from "./queries";

export const useHandlers = () => {
  const {
    state: {
      aggregatedData,
      canvasRef,
      currentTime,
      currentNode,
      intervalId,
      maxTime,
      playing,
      speed,
      simulationPauseTime,
      simulationStartTime,
      topography,
    },
    dispatch,
  } = useGraphContext();

  const { startStream, stopStream } = useStreamMessagesHandler();

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

    const { offsetX, offsetY } = getOffsetCoordinates(
      topography,
      width,
      height,
    );

    // Apply translation and scaling
    context.translate(offsetX, offsetY);
    context.scale(CANVAS_SCALE, CANVAS_SCALE);

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
      context.arc(node.fx, node.fy, 2, 0, 2 * Math.PI);
      context.fillStyle = node.data.stake ? "green" : "blue";

      if (currentNode === node.id.toString()) {
        context.fillStyle = "red";
      }

      context.stroke();
      context.strokeStyle = "black";

      const hasData = aggregatedData.current.nodes.get(node.id.toString());
      if (hasData) {
        context.strokeStyle = "red";
        context.lineWidth = 1;
      }

      context.fill();
    });

    context.restore();
  }, [
    playing,
    speed,
    maxTime,
    topography.nodes,
    topography.links,
    currentNode,
  ]);

  // Function to toggle play/pause
  const togglePlayPause = useCallback(() => {
    if (!playing) {
      startStream(currentTime, speed);
      simulationStartTime.current = performance.now() - simulationPauseTime.current;
      intervalId.current = setInterval(() => {
        const elapsed =
          simulationStartTime.current !== 0
            ? (performance.now() - simulationStartTime.current) * speed
            : 0;

        dispatch({ type: "SET_CURRENT_TIME", payload: elapsed });
      }, 1000 / 60);
    } else {
      stopStream();
      simulationPauseTime.current = performance.now() - simulationStartTime.current;
      clearInterval(intervalId.current);
      intervalId.current = undefined;
    }

    dispatch({ type: "TOGGLE_PLAYING" });
  }, [drawTopography, currentTime, speed, playing]);

  const handleResetSim = useCallback(() => {
    dispatch({
      type: "BATCH_UPDATE",
      payload: {
        currentNode: undefined,
        currentTime: 0,
        playing: false,
        speed: ESpeedOptions["3% Speed"],
      },
    });

    aggregatedData.current = defaultAggregatedData;
    simulationStartTime.current = 0;
    simulationPauseTime.current = 0;

    clearInterval(intervalId.current);
    intervalId.current = undefined;

    drawTopography();
  }, []);

  return {
    handleResetSim,
    drawTopography,
    togglePlayPause,
  };
};
