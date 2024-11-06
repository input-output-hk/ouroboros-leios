"use client"
import { useEffect, useMemo, useRef, useState, type FC } from "react";

import { Slider } from "./Slider";
import { type INodeMap, type ISlot } from "./types";

export const Graph: FC = () => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
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

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) {
      return;
    }

    const context = canvas.getContext("2d");
    if (!context) {
      return;
    }

    const width = 1024;
    const height = 600;

    let scale = 1;
    const zoomSensitivity = 0.1;
    let isDragging = false;
    let startX: number, startY: number;

    // Set canvas dimensions
    canvas.width = width;
    canvas.height = height;

    // Define the particle
    // const particle = { x: nodes[0].x, y: nodes[0].y };
    // Calculate the bounds
    const xValues = refNodes.map(({ fx }) => fx);
    const yValues = refNodes.map(({ fy }) => fy);
    const minX = Math.min(...xValues);
    const maxX = Math.max(...xValues);
    const minY = Math.min(...yValues);
    const maxY = Math.max(...yValues);

    const pathWidth = maxX - minX;
    const pathHeight = maxY - minY;

    // Compute the canvas center
    const canvasCenterX = canvas.width / 2;
    const canvasCenterY = canvas.height / 2;

    // Calculate the offset to center the path
    let offsetX = canvasCenterX - (minX + pathWidth / 2);
    let offsetY = canvasCenterY - (minY + pathHeight / 2);

    // Function to draw the scene
    const draw = () => {
      // Clear the canvas
      context.clearRect(0, 0, width, height);

      context.save();


      // Apply translation
      context.translate(offsetX, offsetY);
      context.scale(scale, scale);

      // Draw the links
      refLinks.forEach(n => {
        const nodeStart = refNodes.find(({ id }) => id === n.source);
        const nodeEnd = refNodes.find(({ id }) => id === n.target);
        if (!nodeStart || !nodeEnd) {
          return;
        }
        
        context.beginPath();
        context.moveTo(nodeStart.fx, nodeStart.fy);
        context.lineTo(nodeEnd.fx, nodeEnd.fy);
        context.strokeStyle = "#ddd";
        context.lineWidth = 1;
        context.stroke();
      })

      // Draw the nodes
      refNodes.forEach(n => {
        context.beginPath();
        context.arc(n.fx, n.fy, 6, 0, 2 * Math.PI)
        context.fillStyle = n.data.stake ? "green" : "blue";
        context.fill();
      })

      // Draw the particle
      context.beginPath();
      // context.arc(particle.x, particle.y, 5, 0, 2 * Math.PI);
      context.fillStyle = "red";
      context.fill();

      context.restore();
    }

    canvas.addEventListener('mousedown', (event) => {
      // Start dragging
      isDragging = true;
    
      // Get the initial mouse position
      const rect = canvas.getBoundingClientRect();
      startX = event.clientX - rect.left;
      startY = event.clientY - rect.top;
    });
    
    canvas.addEventListener('mousemove', (event) => {
      if (isDragging) {
        // Calculate how far the mouse has moved
        const rect = canvas.getBoundingClientRect();
        const mouseX = event.clientX - rect.left;
        const mouseY = event.clientY - rect.top;
    
        // Update the translation offsets
        offsetX += (mouseX - startX) / scale;
        offsetY += (mouseY - startY) / scale;
    
        // Update the starting position for the next move event
        startX = mouseX;
        startY = mouseY;
    
        // Redraw the canvas
        draw();
      }
    });
    
    canvas.addEventListener('mouseup', () => {
      // Stop dragging
      isDragging = false;
    });
    
    canvas.addEventListener('mouseout', () => {
      // Stop dragging if the mouse leaves the canvas
      isDragging = false;
    });

    canvas.addEventListener('wheel', (event) => {
      // Prevent the default scrolling behavior
      event.preventDefault();
    
      // Calculate the new scale factor
      const zoom = event.deltaY > 0 ? 1 - zoomSensitivity : 1 + zoomSensitivity;
      scale *= zoom;
    
      // Redraw the canvas with the new scale
      draw();
    });

    draw();

    // Function to animate the particle
    const animateParticle = () => {
      const duration = 2000; // duration of the animation in milliseconds
      const startTime = Date.now();

      function animate() {
        const elapsed = Date.now() - startTime;
        const t = Math.min(elapsed / duration, 1); // Normalize time to [0, 1]

        // Interpolate the particle's position
        // particle.x = nodes[0].x + (nodes[1].x - nodes[0].x) * t;
        // particle.y = nodes[0].y + (nodes[1].y - nodes[0].y) * t;

        // Draw the scene
        draw();

        if (t < 1) {
          requestAnimationFrame(animate); // Continue the animation
        } else {
          animateParticle(); // Restart the animation
        }
      }

      animate();
    }

    // Start the animation
    // animateParticle();
  }, [refLinks, refNodes]); // Empty dependency array to run once when the component mounts

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

  // console.log(fgRef.current.d3Force())

  if (!refNodes || !refLinks) {
    return <p>Loading...</p>
  }

  return (
    <div className="container mx-auto">
      <div className="flex items-center justify-center gap-4 my-4 max-w-3xl mx-auto">
        <Slider value={currentMessageIndex} setValue={setCurrentMessageIndex} />
        <button className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2" onClick={() => setPlay(prev => !prev)}>{play ? "Stop" : "Start"}</button>
      </div>
      <canvas ref={canvasRef} />
      {/* <ForceGraph2D
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
      /> */}
    </div>
  );
}
