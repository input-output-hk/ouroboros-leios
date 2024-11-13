"use client";
import {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
  type FC,
} from "react";

import { Slider } from "./Slider";
import {
  EMessageType,
  IServerMessage,
  ITransactionGenerated,
  ITransactionMessage,
  ITransactionReceived,
  ITransactionSent,
  ITransformedNodeMap,
} from "./types";

interface IGraphProps {
  messages: IServerMessage[];
  topography: ITransformedNodeMap;
}

const width = 1024;
const height = 600;
const zoomSensitivity = 0.1;
let scale = 2,
  isDragging = false,
  startX: number,
  startY: number,
  offsetX = 0,
  offsetY = 0;

export const Graph: FC<IGraphProps> = ({ messages, topography }) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const simulationStart = useRef(performance.now());
  const [play, setPlay] = useState(false);
  const [currentTime, setCurrentTime] = useState(0);
  const [speed, setSpeed] = useState<1 | 2 | 3>(3);

  const transactions = useMemo(() => {
    const transactionsById: Map<number, ITransactionMessage[]> = new Map();

    const generatedMessages = messages.filter(
      ({ message }) => message.type === EMessageType.TransactionGenerated
    ) as IServerMessage<ITransactionGenerated>[];
    const sentMessages = messages.filter(
      ({ message }) => message.type === EMessageType.TransactionSent
    ) as IServerMessage<ITransactionSent>[];
    const receivedMessages = messages.filter(
      ({ message }) => message.type === EMessageType.TransactionReceived
    ) as IServerMessage<ITransactionReceived>[];

    for (const input of generatedMessages) {
      const transactionList: ITransactionMessage[] = [];

      for (const sentMsg of sentMessages) {
        if (sentMsg.message.id === input.message.id) {
          const receivedMsg = receivedMessages.find(
            (r) =>
              r.message.id === input.message.id &&
              r.message.sender === sentMsg.message.sender &&
              r.message.recipient === sentMsg.message.recipient
          );

          if (!receivedMsg) {
            console.log(
              "Could not find matching transaction for " + sentMsg.message.id
            );
            continue;
          }

          // Convert time to miliseconds from nanoseconds.
          transactionList.push({
            duration:
              Math.floor(receivedMsg.time / 10000) -
              Math.floor(sentMsg.time / 10000),
            source: sentMsg.message.sender,
            target: sentMsg.message.recipient,
            sentTime: Math.floor(sentMsg.time / 10000),
            generated: Math.floor(input.time / 10000),
          });
        }
      }

      transactionsById.set(input.message.id, transactionList);
    }

    return transactionsById;
  }, [messages]);

  // Function to draw the scene
  const draw = useCallback(() => {
    const canvas = canvasRef.current;
    const context = canvas?.getContext("2d");
    if (!context || !canvas) {
      return;
    }

    // Current time in simulation
    const simulationTime = (performance.now() - simulationStart.current) * speed;

    // Set canvas dimensions
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
    for (const { fx, fy } of topography.nodes) {
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
    offsetX = canvasCenterX - (minX + pathWidth / 2);
    offsetY = canvasCenterY - (minY + pathHeight / 2);

    // Apply translation and scaling
    context.translate(offsetX, offsetY);
    context.scale(scale, scale);

    // Draw the links
    topography.links.forEach((link) => {
      const nodeStart = topography.nodes.find(({ id }) => id === link.source);
      const nodeEnd = topography.nodes.find(({ id }) => id === link.target);
      if (!nodeStart || !nodeEnd) {
        return;
      }

      context.beginPath();
      context.moveTo(nodeStart.fx, nodeStart.fy);
      context.lineTo(nodeEnd.fx, nodeEnd.fy);
      context.strokeStyle = "#ddd";
      context.lineWidth = 1;
      context.stroke();
    });

    // Draw the transactions
    transactions.forEach((txList) => {
      txList.forEach((transaction) => {
        const { duration, source, target, sentTime } = transaction;
        const sourceNode = topography.nodes.find((n) => n.id === source);
        const targetNode = topography.nodes.find((n) => n.id === target);

        if (!sourceNode || !targetNode) {
          console.log("Could not find source and target nodes for this transaction.");
          return;
        }

        const startX = sourceNode.fx;
        const startY = sourceNode.fy;
        const endX = targetNode.fx;
        const endY = targetNode.fy;
        const elapsed = simulationTime - sentTime;

        if (elapsed > duration || elapsed < 0) return; // Skip if the animation is done or hasn't started

        // Calculate the interpolation factor
        const t = elapsed / duration;
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
      context.arc(node.fx, node.fy, 6, 0, 2 * Math.PI);
      context.fillStyle = node.data.stake ? "green" : "blue";
      context.fill();
    });

    context.restore();

    if (play) {
      requestAnimationFrame(draw);
    }
  }, [topography, transactions, play, speed]);

  // Function to toggle play/pause
  const togglePlayPause = () => {
    setPlay((prevPlay) => !prevPlay);
  };

  // Function to reset the simulation
  const resetSimulation = () => {
    setPlay(false);
    setCurrentTime(0);
    simulationStart.current = performance.now(); // Reset start time
  };

  // Effect to start/stop the animation loop
  useEffect(() => {
    if (play) {
      simulationStart.current = performance.now();
      requestAnimationFrame(draw);
    }
  }, [play, draw]);

  // Effect to update the simulation time
  useEffect(() => {
    let interval: NodeJS.Timer | undefined;
    if (play) {
      interval = setInterval(() => {
        setCurrentTime((prev) => prev + speed);
      }, 1000 / 60); // 60 FPS
    } else {
      clearInterval(interval);
    }
    
    return () => clearInterval(interval);
  }, [play, speed]);

  // Initial draw on mount
  useEffect(() => {
    draw();
  }, [draw]);

  if (!topography.links.length || !topography.nodes.length) {
    return <p>Loading...</p>;
  }

  return (
    <div className="container mx-auto">
      <div className="flex items-center justify-center gap-4 my-4 max-w-3xl mx-auto">
        <Slider value={currentTime} max={messages[messages.length - 1].time} setValue={setCurrentTime} />
        <button
          className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
          onClick={togglePlayPause}
        >
          {play ? "Pause" : "Play"}
        </button>
        <button
          className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
          onClick={resetSimulation}
        >
          Reset
        </button>
      </div>
      <canvas ref={canvasRef} />
    </div>
  );
};
