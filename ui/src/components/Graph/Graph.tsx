"use client"
import { useEffect, useMemo, useRef, useState, type FC } from "react";
import { ForceGraph2D } from "react-force-graph";

import { Slider } from "./Slider";
import { type INodeMap, type ISlot } from "./types";

export const Graph: FC = () => {
  const fgRef = useRef();
  const [nodeMap, setNodeMap] = useState<INodeMap>({
    nodes: [],
    links: []
  });
  const [play, setPlay] = useState(false);
  const [currentMessageIndex, setCurrentMessageIndex] = useState(0);
  const [messages, setMessages] = useState<ISlot[]>([]);
  const [blockProducers, setBlockProducers] = useState<Set<number>>(new Set());

  useEffect(() => {
    (async () => {
      await fetch("/api/messages").then(async ({ body }) => {
        if (!body) {
          return;
        }
  
        const reader = body.getReader();
          const decoder = new TextDecoder();
          while(true) {
            const { done, value } = await reader.read();
            if (done) {
              break;
            }
  
            const jsonl = decoder.decode(value);
            jsonl.split(/\n/).forEach(line => {
              if (!line) {
                return;
              }
              
              try {
                const slot = JSON.parse(line);
                setMessages(prev => {
                  const newMessages = [...prev];
                  newMessages.push(slot);
                  return newMessages;
                })
              } catch (e) {
                console.log(`Failed to parse JSON: ${line}`)
              }
            })
          }
      });

      await fetch("/api/topography").then(async ({ body }) => {
        if (!body) {
          return;
        }
  
        const reader = body.getReader();
        const decoder = new TextDecoder();
        while(true) {
          const { done, value } = await reader.read();
          if (done) {
            break;
          }

          try {
            const json: INodeMap = JSON.parse(decoder.decode(value));
            setNodeMap(prev => {
              const newMap = {...prev};
              newMap.links = newMap.links.concat(json.links);
              newMap.nodes = newMap.nodes.concat(json.nodes);

              return newMap;
            })
          } catch (e) {
            console.log(e);
          }
        }
      })
    })()
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

  // useEffect(() => {
  //   if (!messages || !refLinks || !fgRef.current) {
  //     return;
  //   }

  //   const currentMessage = messages[currentMessageIndex].message;
  //   if (currentMessage.type === EMessageType.TransactionReceived) {
  //     // @ts-expect-error source and target get mutated with node data.
  //     const link = refLinks.find(({ source, target }) => source.id === currentMessage.data.sender && target.id === currentMessage.data.recipient);

  //     if (link) {
  //       // @ts-expect-error There are no instance exports, lame.
  //       fgRef.current.emitParticle(link);
  //     }
  //   }

  //   if (currentMessage.type === EMessageType.InputBlockGenerated) {
  //     const blockProducerId = currentMessage.data.producer;
  //     setBlockProducers(prev => new Set(prev).add(blockProducerId));
  //     setTimeout(() => {
  //       setBlockProducers(prev => {
  //         const newSet = new Set(prev)
  //         newSet.delete(blockProducerId)
  //         return newSet;
  //       })
  //     }, 1000)
  //   }
  // }, [currentMessageIndex, messages, refLinks, play])

  // useEffect(() => {
  //   let interval: Timer | undefined;
  //   if (!interval && play) {
  //     interval = setInterval(() => setCurrentMessageIndex(prev => prev + 1), 1000);
  //   }

  //   if (interval && !play) {
  //     clearInterval(interval);
  //   }

  //   return () => interval && clearInterval(interval);
  // }, [play])

  // const simulation = useMemo(() => d3.forceSimulation(refNodes), [refNodes])
  // console.log(simulation)

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
