"use client";
import {
  startTransition,
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
  type FC,
} from "react";

import { CartesianGrid, Line, LineChart, ResponsiveContainer, Tooltip, TooltipProps, XAxis, YAxis } from "recharts";
import { NameType, ValueType } from "recharts/types/component/DefaultTooltipContent";
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

enum ESpeedOptions {
  "1x" = 0.1,
  "2x" = 0.2,
  "3x" = 0.3,
}

const scale = 3;
let offsetX = 0,
  offsetY = 0;

  const CustomTooltip = ({ active, payload, label }: TooltipProps<ValueType, NameType>) => {
    if (active && payload && payload.length) {
      console.log(payload)
      return (
        <div className="custom-tooltip">
          <p className="label">{`Message: #${payload[0].payload.message}`}</p>
          <p className="intro">{`Time Sent: ${payload[0].payload.time}ms`}</p>
        </div>
      );
    }
  
    return null;
  };

export const Graph: FC<IGraphProps> = ({ messages, topography }) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const simulationStart = useRef(performance.now());
  const pauseTime = useRef<number | null>(null);
  const animationFrameId = useRef<number | null>(null);
  const [currentTime, setCurrentTime] = useState<number>(0);
  const [play, setPlay] = useState(false);
  const [speed, setSpeed] = useState<ESpeedOptions>(ESpeedOptions["1x"]);
  const [sentMessages, setSentMessages] = useState<Set<string>>(new Set());
  const maxTime = useMemo(
    () => Math.floor(messages[messages.length - 1].time / 1000000),
    [messages, speed],
  );

  const data = useMemo(() => [...sentMessages.values()].map((v, index) => ({
    message: index + 1,
    time: Number(v.split("#")[1])
  })), [sentMessages.size])

  const transactions = useMemo(() => {
    const transactionsById: Map<number, ITransactionMessage[]> = new Map();

    const generatedMessages = messages.filter(
      ({ message }) => message.type === EMessageType.TransactionGenerated,
    ) as IServerMessage<ITransactionGenerated>[];
    const sentMessages = messages.filter(
      ({ message }) => message.type === EMessageType.TransactionSent,
    ) as IServerMessage<ITransactionSent>[];
    const receivedMessages = messages.filter(
      ({ message }) => message.type === EMessageType.TransactionReceived,
    ) as IServerMessage<ITransactionReceived>[];

    for (const generatedMsg of generatedMessages) {
      const transactionList: ITransactionMessage[] = [];

      for (const sentMsg of sentMessages) {
        if (sentMsg.message.id === generatedMsg.message.id) {
          const receivedMsg = receivedMessages.find(
            (r) =>
              r.message.id === generatedMsg.message.id &&
              r.message.sender === sentMsg.message.sender &&
              r.message.recipient === sentMsg.message.recipient,
          );

          if (!receivedMsg) {
            console.log(
              "Could not find matching transaction for " + sentMsg.message.id,
            );
            continue;
          }

          // Convert time from nanoseconds to miliseconds.
          transactionList.push({
            id: generatedMsg.message.id,
            duration:
              Math.floor(receivedMsg.time / 1000000) -
              Math.floor(sentMsg.time / 1000000),
            source: sentMsg.message.sender,
            target: sentMsg.message.recipient,
            sentTime: Math.floor(sentMsg.time / 1000000),
            generated: Math.floor(generatedMsg.time / 1000000),
          });
        }
      }

      transactionsById.set(generatedMsg.message.id, transactionList);
    }

    return transactionsById;
  }, [messages]);

  const maxTransactions = useMemo(() => transactions.values().reduce((t, v) => t += v.length, transactions.size), [transactions.size])

  // Function to draw the scene
  const draw = useCallback(() => {
    const canvas = canvasRef.current;
    const context = canvas?.getContext("2d");
    if (!context || !canvas) {
      return;
    }

    // Current time in simulation
    const simulationTime =
      (performance.now() - simulationStart.current) * speed;

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
    offsetX = canvasCenterX - (minX + pathWidth / 2) * scale;
    offsetY = canvasCenterY - (minY + pathHeight / 2) * scale;

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
        const { duration, source, target, sentTime, id } = transaction;
        const sourceNode = topography.nodes.find((n) => n.id === source);
        const targetNode = topography.nodes.find((n) => n.id === target);

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
        const elapsed = simulationTime - sentTime;

        if (elapsed < 0) {
          return; // Skip if the animation is done or hasn't started
        }

        if (elapsed > duration) {
          setSentMessages((prev) => {
            prev.add(`${id}-${source}-${target}#${sentTime + duration}`);
            return prev;
          });

          return;
        }

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
      context.arc(node.fx, node.fy, 3, 0, 2 * Math.PI);
      context.fillStyle = node.data.stake ? "green" : "blue";
      context.fill();
    });

    context.restore();

    if (play) {
      animationFrameId.current = requestAnimationFrame(draw);
      setCurrentTime((prev) => prev + 1);
    }
  }, [topography, transactions, play, speed]);

  // Function to toggle play/pause
  const togglePlayPause = () => {
    setPlay((playing) => !playing);
    if (!play) {
      simulationStart.current = performance.now() - (pauseTime.current ?? 0);
      animationFrameId.current = requestAnimationFrame(draw);
    } else {
      pauseTime.current = performance.now() - (simulationStart.current ?? 0);
      if (animationFrameId.current) {
        cancelAnimationFrame(animationFrameId.current);
        animationFrameId.current = null;
      }
    }
  };

  // Function to reset the simulation
  const resetSimulation = () => {
    setPlay(false);
    setCurrentTime(0);
    setSpeed(ESpeedOptions["1x"]);
    setSentMessages(new Set());
    simulationStart.current = performance.now();
    pauseTime.current = 0;
    startTransition(draw);

    if (animationFrameId.current) {
      cancelAnimationFrame(animationFrameId.current);
      animationFrameId.current = null;
    }
  };

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
        <Slider
          value={currentTime}
          max={maxTime}
          setValue={(v) => {
            setCurrentTime(Number(v));
          }}
        />
        <button
          className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
          onClick={togglePlayPause}
        >
          {play ? "Pause" : "Play"}
        </button>
        <button
          disabled={play}
          className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
          onClick={resetSimulation}
        >
          Reset
        </button>
        <div className="flex items-center justify-center gap-2">
          <label htmlFor="speed">Speed:</label>
          <select
            id="speed"
            disabled={play}
            onChange={(e) => {
              resetSimulation();
              setSpeed(Number(e.target.value) as ESpeedOptions);
            }}
          >
            {Object.keys(ESpeedOptions)
              .filter((key) => isNaN(Number(key)))
              .map((name) => {
                return (
                  <option
                    key={name}
                    value={ESpeedOptions[name as keyof typeof ESpeedOptions]}
                  >
                    {name}
                  </option>
                );
              })}
          </select>
        </div>
      </div>
      <div className="flex items-center justify-between gap-4">

      <div className="h-[80vh] border-2 border-gray-200 rounded mb-8 w-2/3">
        <div className="flex items-center justify-center gap-4">
          <div><h4>Transactions Sent: {sentMessages.size}</h4></div>
        </div>
        <canvas ref={canvasRef} />
      </div>
      <div className="flex flex-col w-1/3 items-center justify-between gap-4">
        <div className="w-full h-[400px]">
          <ResponsiveContainer width="100%" height="100%">
            <LineChart data={data}>
              <CartesianGrid strokeDasharray="3 3" />
              <XAxis tick={false} label="Transactions Sent" domain={[0, maxTransactions]} allowDataOverflow type="number" dataKey="message" />
              <YAxis tick={false} label="Time" domain={[0, maxTime]} dataKey="time" />
              <Line type="monotone" dataKey="time" stroke="#82ca9d" strokeWidth={2} dot={false} />
              <Tooltip content={props => <CustomTooltip {...props} />} />
            </LineChart>
          </ResponsiveContainer>
        </div>
        <div className="w-full"></div>
        <div className="w-full"></div>
      </div>
    </div>
      </div>
  );
};
