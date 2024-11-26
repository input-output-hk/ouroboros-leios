import { useGraphContext } from "@/contexts/GraphContext/context";
import { ESpeedOptions } from "@/contexts/GraphContext/types";
import { useCallback } from "react";
import { isWithinRange } from "../utils";
import { useStreamMessagesHandler } from "./queries";

const scale = 4;
let offsetX = 0,
  offsetY = 0;

export const useHandlers = () => {
  const {
    state: {
      canvasRef,
      currentTime,
      intervalId,
      maxTime,
      playing,
      transactionsByIdRef,
      txGeneratedMessagesById,
      txReceivedMessagesById,
      txSentMessagesById,
      speed,
      simulationPauseTime,
      simulationStartTime,
      topography,
    },
    dispatch,
  } = useGraphContext();

  const {
    startStream,
    stopStream,
  } = useStreamMessagesHandler();

  const drawCanvas = useCallback(() => {
    const canvas = canvasRef.current;
    const context = canvas?.getContext("2d");
    if (!context || !canvas) {
      return;
    }

    // Current time in simulation
    const now = performance.now();
    const elapsed =
      simulationStartTime.current !== 0
        ? (now - simulationStartTime.current) * speed
        : 0;

    if (elapsed >= maxTime) {
      togglePlayPause();
      return;
    } else {
      dispatch({ type: "SET_CURRENT_TIME", payload: elapsed });
    }

    if (elapsed >= maxTime) {
      intervalId.current && clearInterval(intervalId.current);
      dispatch({ type: "SET_PLAYING", payload: false });
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

    // Apply translation and scaling
    context.translate(offsetX, offsetY);
    context.scale(scale, scale);

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

    // Draw the transactions
    transactionsByIdRef.current.forEach((txList) => {
      txList.forEach((transaction) => {
        const { duration, source, target, sentTime } = transaction;
        const sourceNode = topography.nodes.get(source);
        const targetNode = topography.nodes.get(target);

        if (!sourceNode || !targetNode) {
          console.log(
            "Could not find source and target nodes for this transaction.",
          );
          return;
        }

        const startX = sourceNode.fx;
        const startY = sourceNode.fy;
        const endX = targetNode.fx;
        const endY = targetNode.fy;
        const transactionElapsedTime = elapsed - sentTime;

        // Calculate the interpolation factor
        const t = Math.min(transactionElapsedTime / duration, 1);
        const x = startX + t * (endX - startX);
        const y = startY + t * (endY - startY);

        // Animation hasn't started.
        if (transactionElapsedTime < 0) {
          return;
        }

        // Animation done.
        if (x === endX && y === endY) {
          return;
        }

        // Draw the moving circle
        context.beginPath();
        context.arc(x, y, 1, 0, 2 * Math.PI);
        context.fillStyle = "red";
        context.fill();
      });
    });

    // Draw the nodes
    topography.nodes.forEach((node) => {
      context.beginPath();
      context.arc(node.fx, node.fy, 1, 0, 2 * Math.PI);
      context.fillStyle = node.data.stake ? "green" : "blue";
      context.stroke();
      context.strokeStyle = "black";

      txGeneratedMessagesById.current.forEach((m) => {
        const target = m.time / 1_000_000;
        if (
          m.message.publisher === node.id &&
          isWithinRange(elapsed, target, 50)
        ) {
          context.fillStyle = "red";
        }
      });

      context.fill();
    });

    context.restore();

    if (intervalId.current !== null) {
      intervalId.current = requestAnimationFrame(drawCanvas);
    }
  }, [playing, speed, maxTime, topography.nodes, topography.links]);

  // Function to toggle play/pause
  const togglePlayPause = useCallback(() => {
    const now = performance.now();
    if (!playing) {
      startStream(currentTime, speed);
      simulationStartTime.current = now - simulationPauseTime.current;
      simulationPauseTime.current = now;
      intervalId.current = requestAnimationFrame(drawCanvas);
    } else {
      stopStream();
      simulationPauseTime.current = now - simulationStartTime.current;
      if (intervalId.current !== null) {
        cancelAnimationFrame(intervalId.current);
        intervalId.current = null;
      }
    }

    dispatch({ type: "TOGGLE_PLAYING" });
  }, [drawCanvas, currentTime, speed, playing]);

  const handleResetSim = useCallback(() => {
    dispatch({
      type: "BATCH_UPDATE",
      payload: {
        currentTime: 0,
        playing: false,
        sentTxs: [],
        speed: ESpeedOptions["3% Speed"],
        generatedMessages: [],
      },
    });

    simulationStartTime.current = 0;
    simulationPauseTime.current = 0;
    transactionsByIdRef.current = new Map();
    txReceivedMessagesById.current = new Map();
    txGeneratedMessagesById.current = new Map();
    txSentMessagesById.current = new Map();

    if (intervalId.current) {
      clearInterval(intervalId.current);
      intervalId.current = null;
    }

    drawCanvas();
  }, []);

  return {
    handleResetSim,
    drawCanvas,
    togglePlayPause,
  };
};
