"use client";

import { type FC } from "react";

import { Test } from "@/app/Test";
import { GraphContextProvider } from "@/contexts/GraphContext/GraphContextProvider";
import { Canvas } from "./modules/Canvas";
import { ChartTransactionsSent } from "./modules/Chart.TransactionsSent";
import { Controls } from "./modules/Controls";
import { Slider } from "./modules/Slider";

enum ESpeedOptions {
  "1/10" = 0.1,
  "2/10" = 0.2,
  "3/10" = 0.3,
}

export const MILLISECOND_RANGE = 500;

const scale = 3;
let offsetX = 0,
  offsetY = 0;

// export const Graph: FC = () => {
//   // const [topography, setTopography] = useState<ITransformedNodeMap>({
//   //   links: [],
//   //   nodes: []
//   // });

//   // const [messages, setMessages] = useState<IServerMessage[] | null>(null);

//   // useEffect(() => {
//   //   streamTopography(setTopography)
//   // }, [])

//   // useEffect(() => {
//   //   streamMessages(setMessages, 0);
//   // }, [])

//   const canvasRef = useRef<HTMLCanvasElement>(null);
//   const simulationStart = useRef<number>(0);
//   const simulationPauseTime = useRef<number>(0);
//   const intervalId = useRef<Timer | null>(null);
//   const [currentTime, setCurrentTime] = useState(0);
//   const [play, setPlay] = useState(false);
//   const [speed, setSpeed] = useState<ESpeedOptions>(ESpeedOptions["3/10"]);
//   const [sentTxs, setSentTxs] = useState<Set<string>>(new Set());
//   const [generatedTxs, setGeneratedTxs] = useState<Set<number>>(new Set());
//   const maxTime = useMemo(
//     () => messages ? Math.floor(messages[messages.length - 1].time / 1000000) : 0,
//     [messages],
//   );

//   const data = useMemo(
//     () =>
//       [...sentTxs.values()].map((v, index) => ({
//         message: index + 1,
//         time: Number(v.split("#")[1]),
//       })),
//     [sentTxs.size],
//   );

//   const txGeneratedMessages = useMemo(() => messages?.filter(
//     ({ message }) => message.type === EMessageType.TransactionGenerated,
//   ) as IServerMessage<ITransactionGenerated>[] || [], [messages]);

//   const txSentMessages = useMemo(() => messages?.filter(
//     ({ message }) => message.type === EMessageType.TransactionSent,
//   ) as IServerMessage<ITransactionSent>[] || [], [messages]);

//   const txReceivedMessages = useMemo(() => messages?.filter(
//     ({ message }) => message.type === EMessageType.TransactionReceived,
//   ) as IServerMessage<ITransactionReceived>[] || [], [messages]);

//   const transactions = useMemo(() => {
//     const transactionsById: Map<number, ITransactionMessage[]> = new Map();

//     for (const generatedMsg of txGeneratedMessages) {
//       const transactionList: ITransactionMessage[] = [];

//       for (const sentMsg of txSentMessages) {
//         if (sentMsg.message.id === generatedMsg.message.id) {
//           const receivedMsg = txReceivedMessages.find(
//             (r) =>
//               r.message.id === generatedMsg.message.id &&
//               r.message.sender === sentMsg.message.sender &&
//               r.message.recipient === sentMsg.message.recipient,
//           );

//           if (!receivedMsg) {
//             console.log(
//               "Could not find matching transaction for " + sentMsg.message.id,
//             );
//             continue;
//           }

//           // Convert time from nanoseconds to miliseconds.
//           transactionList.push({
//             id: generatedMsg.message.id,
//             duration:
//               Math.floor(receivedMsg.time / 1000000) -
//               Math.floor(sentMsg.time / 1000000),
//             source: sentMsg.message.sender,
//             target: sentMsg.message.recipient,
//             sentTime: Math.floor(sentMsg.time / 1000000),
//             generated: Math.floor(generatedMsg.time / 1000000),
//           });
//         }
//       }

//       transactionsById.set(generatedMsg.message.id, transactionList);
//     }

//     return transactionsById;
//   }, [txGeneratedMessages, txSentMessages]);

//   const maxTransactions = useMemo(
//     () =>
//       [...transactions.values()].reduce(
//         (t, v) => (t += v.length),
//         transactions.size,
//       ),
//     [transactions.size],
//   );

//   // Function to draw the scene
//   const draw = useCallback(() => {
//     const canvas = canvasRef.current;
//     const context = canvas?.getContext("2d");
//     if (!context || !canvas) {
//       return;
//     }

//     // Current time in simulation
//     const now = performance.now();
//     const elapsed =
//       simulationStart.current !== 0
//         ? (now - simulationStart.current) * speed
//         : 0;
//     setCurrentTime(elapsed);

//     if (elapsed >= maxTime) {
//       intervalId.current && clearInterval(intervalId.current);
//       setPlay(false);
//       return;
//     }

//     // Set canvas dimensions
//     const width = canvas.parentElement?.getBoundingClientRect().width || 1024;
//     const height = canvas.parentElement?.getBoundingClientRect().height || 800;
//     canvas.width = width;
//     canvas.height = height;

//     // Clear the canvas
//     context.clearRect(0, 0, width, height);
//     context.save();

//     // Calculate the bounds
//     const coordinates: { xValues: number[]; yValues: number[] } = {
//       xValues: [],
//       yValues: [],
//     };
//     for (const { fx, fy } of topography.nodes) {
//       coordinates.xValues.push(fx);
//       coordinates.yValues.push(fy);
//     }
//     const minX = Math.min(...coordinates.xValues);
//     const maxX = Math.max(...coordinates.xValues);
//     const minY = Math.min(...coordinates.yValues);
//     const maxY = Math.max(...coordinates.yValues);

//     const pathWidth = maxX - minX;
//     const pathHeight = maxY - minY;

//     // Compute the canvas center
//     const canvasCenterX = width / 2;
//     const canvasCenterY = height / 2;

//     // Calculate the offset to center the path
//     offsetX = canvasCenterX - (minX + pathWidth / 2) * scale;
//     offsetY = canvasCenterY - (minY + pathHeight / 2) * scale;

//     // Apply translation and scaling
//     context.translate(offsetX, offsetY);
//     context.scale(scale, scale);

//     // Draw the links
//     topography.links.forEach((link) => {
//       const nodeStart = topography.nodes.find(({ id }) => id === link.source);
//       const nodeEnd = topography.nodes.find(({ id }) => id === link.target);
//       if (!nodeStart || !nodeEnd) {
//         return;
//       }

//       context.beginPath();
//       context.moveTo(nodeStart.fx, nodeStart.fy);
//       context.lineTo(nodeEnd.fx, nodeEnd.fy);
//       context.strokeStyle = "#ddd";
//       context.lineWidth = 1;
//       context.stroke();
//     });

//     // Draw the transactions
//     transactions.forEach((txList) => {
//       txList.forEach((transaction) => {
//         const { duration, source, target, sentTime, id } = transaction;
//         const sourceNode = topography.nodes.find((n) => n.id === source);
//         const targetNode = topography.nodes.find((n) => n.id === target);

//         if (!sourceNode || !targetNode) {
//           console.log(
//             "Could not find source and target nodes for this transaction.",
//           );
//           return;
//         }

//         const startX = sourceNode.fx;
//         const startY = sourceNode.fy;
//         const endX = targetNode.fx;
//         const endY = targetNode.fy;
//         const transactionElapsedTime = elapsed - sentTime;

//         if (transactionElapsedTime < 0) {
//           return; // Skip if the animation is done or hasn't started
//         }

//         if (transactionElapsedTime > duration) {
//           setSentTxs((prev) => {
//             prev.add(`${id}-${source}-${target}#${sentTime + duration}`);
//             return prev;
//           });

//           return;
//         }

//         // Calculate the interpolation factor
//         const t = transactionElapsedTime / duration;
//         const x = startX + t * (endX - startX);
//         const y = startY + t * (endY - startY);

//         // Draw the moving circle
//         context.beginPath();
//         context.arc(x, y, 2, 0, 2 * Math.PI);
//         context.fillStyle = "red";
//         context.fill();
//       });
//     });

//     // Draw the nodes
//     topography.nodes.forEach((node) => {
//       context.beginPath();
//       context.arc(node.fx, node.fy, 3, 0, 2 * Math.PI);
//       context.fillStyle = node.data.stake ? "green" : "blue";
//       context.stroke();
//       context.strokeStyle = "black";

//       txGeneratedMessages.forEach(m => {
//         const target = m.time / 1_000_000;
//         if (m.message.publisher === node.id && isWithinRange(elapsed, target, MILLISECOND_RANGE)) {
//           context.fillStyle = "red";
//         }

//         if (m.message.publisher === node.id && elapsed > target) {
//           setGeneratedTxs(prev => {
//             prev.add(m.time);
//             return prev;
//           });
//         }
//       })

//       context.fill();
//     });

//     context.restore();
//   }, [topography, transactions, play, speed, maxTime, txGeneratedMessages]);

//   // Function to toggle play/pause
//   const togglePlayPause = useCallback(() => {
//     startTransition(() => {
//       const now = performance.now();
//       if (!play) {
//         simulationStart.current = now - simulationPauseTime.current;
//         simulationPauseTime.current = now;
//         intervalId.current = setInterval(draw, 1000 / 120); // 120 FPS
//       } else {
//         simulationPauseTime.current = now - simulationStart.current;
//         if (intervalId.current) {
//           clearInterval(intervalId.current);
//           intervalId.current = null;
//         }
//       }

//       setPlay((playing) => {
//         return !playing;
//       });
//     });
//   }, [draw]);

//   // Function to reset the simulation
//   const resetSimulation = () => {
//     setPlay(false);
//     setCurrentTime(0);
//     setSpeed(ESpeedOptions["1/10"]);
//     setSentTxs(new Set());
//     simulationStart.current = 0;
//     simulationPauseTime.current = 0;

//     if (intervalId.current) {
//       clearInterval(intervalId.current);
//       intervalId.current = null;
//     }

//     draw();
//   };

//   // Clear the interval on unmount
//   useEffect(() => {
//     return () => {
//       if (intervalId.current) {
//         clearInterval(intervalId.current);
//       }
//     };
//   }, []);

//   useEffect(() => {
//     draw();
//   }, []);

//   if (!topography.links.length || !topography.nodes.length) {
//     return <p>Loading...</p>;
//   }

//   return (
//     <div className="container mx-auto">
//       <div className="flex items-center justify-between gap-4">
//         <div className="flex flex-col w-1/3 items-center justify-between gap-4">
//           <div className="w-full h-[400px]">
//             <ResponsiveContainer width="100%" height="100%">
//               <AreaChart data={data}>
//                 <CartesianGrid strokeDasharray="3 3" />
//                 <XAxis
//                   tick={false}
//                   label="Transactions Sent"
//                   domain={[0, maxTransactions]}
//                   allowDataOverflow
//                   type="number"
//                   dataKey="message"
//                 />
//                 <YAxis
//                   tick={false}
//                   label="Time"
//                   domain={[0, maxTime]}
//                   dataKey="time"
//                 />
//                 <Area
//                   type="monotone"
//                   dataKey="time"
//                   stroke="#8884d8"
//                   fill="#8884d8"
//                   strokeWidth={2}
//                   dot={false}
//                 />
//                 <Tooltip content={(props) => <CustomTooltip {...props} />} />
//               </AreaChart>
//             </ResponsiveContainer>
//           </div>
//           <div className="w-full"></div>
//           <div className="w-full"></div>
//         </div>
//       </div>
//     </div>
//   );
// };

export const Graph: FC = () => {
  return (
    <GraphContextProvider>
      <Test />
      <div className="container mx-auto">
        <div className="flex items-center justify-center gap-4 my-4 max-w-3xl mx-auto">
          <Slider />
          <Controls />
        </div>
        
        <div className="flex items-center justify-between gap-4">
          <Canvas />  
          <div className="flex flex-col w-1/3 items-center justify-between gap-4">
            <div className="w-full h-[400px]">
              <ChartTransactionsSent />
            </div>
          </div>
        </div>
      </div>
    </GraphContextProvider>
  );
};
