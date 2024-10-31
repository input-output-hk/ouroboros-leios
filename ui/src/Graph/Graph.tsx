import { useEffect, useMemo, useRef, useState, type FC } from "react";
import { ForceGraph2D } from "react-force-graph";

import { Slider } from "./Slider";
import { EMessageType, type IMessage, type INodeMap } from "./types";

export const Graph: FC = () => {
  const fgRef = useRef();
  const [nodeMap, setNodeMap] = useState<INodeMap>();
  const [messages, setMessages] = useState<IMessage[]>();
  const [play, setPlay] = useState(false);
  const [currentMessageIndex, setCurrentMessageIndex] = useState(0);
  const [blockProducers, setBlockProducers] = useState<Set<number>>(new Set());
  const containerRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    import("./files/message.json").then(m => {
      const result = m.default.messages.map(({ time, message }) => {
        const { type, ...rest } = message;
        return {
          time,
          message: {
            type,
            data: rest
          }
        }
      });

      setMessages(result as IMessage[]);
    });

    import("./files/nodes.json").then(m => {
      const result: INodeMap = {
        links: m.default.links,
        nodes: m.default.nodes
      };
      setNodeMap(result);
    })

    console.log(fgRef.current)
  }, [])

  const { refNodes, refLinks } = useMemo(() => {
    const nodes = nodeMap?.nodes.map((n, i) => ({
      id: i,
      fx: n.location[0],
      fy: n.location[1],
      data: n
    }));

    const links = nodeMap?.links.map((l) => ({
      source: l.nodes[0],
      target: l.nodes[1],
    }));

    return {
      refNodes: nodes,
      refLinks: links
    }
  }, [nodeMap]);

  useEffect(() => {
    if (!messages || !refLinks || !fgRef.current) {
      return;
    }

    const currentMessage = messages[currentMessageIndex].message;
    if (currentMessage.type === EMessageType.TransactionReceived) {
      // @ts-expect-error source and target get mutated with node data.
      const link = refLinks.find(({ source, target }) => source.id === currentMessage.data.sender && target.id === currentMessage.data.recipient);

      if (link) {
        // @ts-expect-error There are no instance exports, lame.
        fgRef.current.emitParticle(link);
      }
    }

    if (currentMessage.type === EMessageType.InputBlockGenerated) {
      const blockProducerId = currentMessage.data.producer;
      setBlockProducers(prev => new Set(prev).add(blockProducerId));
      setTimeout(() => {
        setBlockProducers(prev => {
          const newSet = new Set(prev)
          newSet.delete(blockProducerId)
          return newSet;
        })
      }, 1000)
    }
  }, [currentMessageIndex, messages, refLinks, play])

  useEffect(() => {
    let interval: Timer | undefined;
    if (!interval && play) {
      interval = setInterval(() => setCurrentMessageIndex(prev => prev + 1), 1000);
    }

    if (interval && !play) {
      clearInterval(interval);
    }

    return () => interval && clearInterval(interval);
  }, [play])

  if (!refNodes || !refLinks) {
    return <p>Loading...</p>
  }

  return (
    <div className="container mx-auto">
      <div className="flex items-center justify-center gap-4 my-4 max-w-3xl mx-auto">
        <Slider value={currentMessageIndex} setValue={setCurrentMessageIndex} />
        <button className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2" onClick={() => setPlay(prev => !prev)}>{play ? "Stop" : "Start"}</button>
      </div>
      <ForceGraph2D
        ref={fgRef}
        width={1920}
        height={1080}
        linkDirectionalParticleColor={() => 'red'}
        linkDirectionalParticleWidth={6}
        linkHoverPrecision={10}
        graphData={{
          nodes: refNodes,
          links: refLinks
        }}
        nodeColor={node => {
          if (blockProducers.has(node.id)) {
            return "green";
          }

          if (node.data.stake) {
            return "red";
          }

          return "blue";
        }}
        onNodeDragEnd={(node) => {
          node.fx = node.data.location[0];
          node.fy = node.data.location[1];
        }}
      />
    </div>
  );
}