import { useGraphContext } from "@/contexts/GraphContext/context";
import { ESpeedOptions } from "@/contexts/GraphContext/types";
import { startTransition, useCallback, useMemo } from "react";
import { MILLISECOND_RANGE } from "../Graph";
import { EMessageType, IServerMessage, ITransactionGenerated } from "../types";
import { isWithinRange } from "../utils";

const scale = 3;
let offsetX = 0,
  offsetY = 0;

export const useHandlers = () => {
  const {
    canvasRef,
    intervalId,
    maxTime,
    messages,
    playing,
    speed,
    setSentTxs,
    setCurrentTime,
    setGeneratedMessages,
    setPlaying,
    setSpeed,
    simulationPauseTime,
    simulationStartTime,
    transactions,
    topography,
  } = useGraphContext();

  const txGeneratedMessages = useMemo(
    () =>
      (messages?.filter(
        ({ message }) => message.type === EMessageType.TransactionGenerated,
      ) as IServerMessage<ITransactionGenerated>[]) || [],
    [messages],
  );

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
    setCurrentTime(elapsed);

    if (elapsed >= maxTime) {
      intervalId.current && clearInterval(intervalId.current);
      setPlaying(false);
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
      context.lineWidth = 0.5;
      context.stroke();
    });

    // Draw the transactions
    transactions.forEach((txList) => {
      txList.forEach((transaction) => {
        const { duration, source, target, sentTime, id } = transaction;
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

        if (transactionElapsedTime < 0) {
          return; // Skip if the animation is done or hasn't started
        }

        if (transactionElapsedTime > duration) {
          setSentTxs((prev) => {
            prev.add(`${id}-${source}-${target}#${sentTime + duration}`);
            return prev;
          });

          return;
        }

        // Calculate the interpolation factor
        const t = transactionElapsedTime / duration;
        const x = startX + t * (endX - startX);
        const y = startY + t * (endY - startY);

        // Draw the moving circle
        context.beginPath();
        context.arc(x, y, 2, 0, 2 * Math.PI);
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

      txGeneratedMessages.forEach((m) => {
        const target = m.time / 1_000_000;
        if (
          m.message.publisher === node.id &&
          isWithinRange(elapsed, target, MILLISECOND_RANGE)
        ) {
          context.fillStyle = "red";
        }

        if (m.message.publisher === node.id && elapsed > target) {
          setGeneratedMessages((prev) => {
            prev.add(m.time);
            return prev;
          });
        }
      });

      context.fill();
    });

    context.restore();
  }, [topography, transactions, playing, speed, maxTime, txGeneratedMessages]);

  // Function to toggle play/pause
  const togglePlayPause = useCallback(() => {
    startTransition(() => {
      const now = performance.now();
      if (!playing) {
        simulationStartTime.current = now - simulationPauseTime.current;
        simulationPauseTime.current = now;
        intervalId.current = setInterval(drawCanvas, 1000 / 120); // 120 FPS
      } else {
        simulationPauseTime.current = now - simulationStartTime.current;
        if (intervalId.current) {
          clearInterval(intervalId.current);
          intervalId.current = null;
        }
      }

      setPlaying((playing) => !playing);
    });
  }, [drawCanvas]);

  const handleResetSim = useCallback(() => {
    setCurrentTime(0);
    setPlaying(false);
    setSentTxs(new Set());
    setSpeed(ESpeedOptions["3/10"]);
    simulationStartTime.current = 0;
    simulationPauseTime.current = 0;

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
