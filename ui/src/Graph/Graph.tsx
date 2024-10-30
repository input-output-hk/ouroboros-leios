import { useEffect, useRef, useState, type FC } from "react";
import { ForceGraph2D } from "react-force-graph";

import { EMessageType, type IMessage, type INodeMap } from "./types";

export const Graph: FC = () => {
  const fgRef = useRef();
  const [nodeMap, setNodeMap] = useState<INodeMap>();
  const [messages, setMessages] = useState<IMessage[]>();

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
  }, [])

  useEffect(() => {
    debugger;
    if (!messages || !fgRef.current || !links) {
      return;
    }

    let lastMessage = 0;
    const interval = setInterval(() => {
      const currentMessage = messages[lastMessage].message;
      if (currentMessage.type === EMessageType.TransactionReceived) {
        // @ts-expect-error source and target get mutated with node data.
        const link = links.find(({ source, target }) => source.id === currentMessage.data.sender && target.id === currentMessage.data.recipient);
        if (link) {
          // @ts-expect-error There are no instance exports, lame.
          fgRef.current.emitParticle(link);
          console.log('emitted')
        }
      }

      lastMessage++;
    }, 1000);

    return () => {
      clearInterval(interval);
    }
  }, [links, messages])

  if (!nodes || !links) {
    return <p>Loading...</p>
  }

  return (
    <ForceGraph2D ref={fgRef}
      linkDirectionalParticleColor={() => 'red'}
      linkDirectionalParticleWidth={6}
      linkHoverPrecision={10}
      graphData={{
        nodes,
        links
      }}
      height={1024}
      width={1920}
      nodeColor={node => {
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
  );
}