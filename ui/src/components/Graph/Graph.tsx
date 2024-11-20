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

const scale = 2;
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
