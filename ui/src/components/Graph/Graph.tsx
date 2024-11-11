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
import { EMessageType, IServerMessage, ITransformedNodeMap } from "./types";

interface IGraphProps {
  messages: IServerMessage[];
  topography: ITransformedNodeMap;
}

const width = 1024;
const height = 600;
const zoomSensitivity = 0.1;
let scale = 1,
  isDragging = false,
  startX: number,
  startY: number,
  offsetX = 0,
  offsetY = 0;

export const Graph: FC<IGraphProps> = ({ messages, topography }) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const [play, setPlay] = useState(false);
  const [currentMessageIndex, setCurrentMessageIndex] = useState(0);
  const [currentTime, setCurrentTime] = useState(0);
  const transactions = useMemo(() => {
    const transactionsById: Map<number, IServerMessage[]> = new Map();

    for (const input of messages) {
      if (
        EMessageType.TransactionGenerated === input.message?.type ||
        EMessageType.TransactionReceived === input.message?.type ||
        EMessageType.TransactionSent === input.message?.type
      ) {
        if (transactionsById.has(input.message.id)) {
          transactionsById.get(input.message.id)?.push(input);
        } else {
          transactionsById.set(input.message.id, [input]);
        }
      }
    }

    return transactionsById;
  }, [messages]);

  console.log(transactions)

  // Function to draw the scene
  const draw = useCallback(() => {
    const canvas = canvasRef.current;
    const context = canvas?.getContext("2d");
    if (!context) {
      return;
    }

    // Clear the canvas
    context.clearRect(0, 0, width, height);
    context.save();

    // Apply translation
    context.translate(offsetX, offsetY);
    context.scale(scale, scale);

    // Draw the particle
    // particles.forEach(p => {
    //   context.beginPath();
    //   context.arc(p.x, p.y, 2, 0 , 2 * Math.PI);
    //   context.fillStyle = "red";
    //   context.fill();
    // })

    // Draw the links
    topography.links.forEach((n) => {
      const nodeStart = topography.nodes.find(({ id }) => id === n.source);
      const nodeEnd = topography.nodes.find(({ id }) => id === n.target);
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

    // Draw the nodes
    topography.nodes.forEach((n) => {
      context.beginPath();
      context.arc(n.fx, n.fy, 6, 0, 2 * Math.PI);
      context.fillStyle = n.data.stake ? "green" : "blue";
      context.fill();
    });

    context.restore();
  }, [currentTime]);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (
      !canvas ||
      !messages.length ||
      !topography.nodes.length ||
      !topography.links.length
    ) {
      return;
    }

    const context = canvas.getContext("2d");
    if (!context) {
      return;
    }

    // Set canvas dimensions
    canvas.width = width;
    canvas.height = height;

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

    canvas.addEventListener("mousedown", (event) => {
      // Start dragging
      isDragging = true;

      // Get the initial mouse position
      const rect = canvas.getBoundingClientRect();
      startX = event.clientX - rect.left;
      startY = event.clientY - rect.top;
    });

    canvas.addEventListener("mousemove", (event) => {
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

    canvas.addEventListener("mouseup", () => {
      // Stop dragging
      isDragging = false;
    });

    canvas.addEventListener("mouseout", () => {
      // Stop dragging if the mouse leaves the canvas
      isDragging = false;
    });

    canvas.addEventListener("wheel", (event) => {
      // Prevent the default scrolling behavior
      event.preventDefault();

      // Calculate the new scale factor
      const zoom = event.deltaY > 0 ? 1 - zoomSensitivity : 1 + zoomSensitivity;
      scale *= zoom;

      // Redraw the canvas with the new scale
      draw();
    });

    // Function to animate the particle
    let slotIndex = 0;
    // const animateParticles = () => {
    //   const slotStartTime = messages[slotIndex].start_time / 100000;
    //   const slotEndTime =
    //     slotIndex === messages.length - 1
    //       ? messages[slotIndex].events[messages[slotIndex].events.length - 1]
    //           .time / 100000
    //       : messages[slotIndex + 1].start_time / 100000;
    //   const duration = slotEndTime - slotStartTime; // duration of the animation in milliseconds
    //   const startTime = Date.now();

    //   function animate() {
    //     const elapsed = Date.now() - startTime;
    //     const t = Math.min(elapsed / duration, 1); // Normalize time to [0, 1]

    //     // Interpolate the particle's position
    //     // for (const message of messages) {
    //     /**
    //      * particles.forEach((p, index) => {
    //      *  const link = refLinks[index];
    //      *
    //      * })
    //      */
    //     // }
    //     // particles.forEach(p => {
    //     //   p.x = nodes[0].x + (nodes[1].x - nodes[0].x) * t;
    //     //   p.y = nodes[0].y + (nodes[1].y - nodes[0].y) * t;
    //     // })

    //     // Draw the scene
    //     draw();

    //     if (t < 1) {
    //       requestAnimationFrame(animate); // Continue the animation
    //       slotIndex++;
    //     }
    //   }

    //   animate();
    // };

    // animateParticles();

    // Start the animation
    // animateParticles();
  }, [topography, messages]); // Empty dependency array to run once when the component mounts

  if (!topography.links.length || !topography.nodes.length) {
    return <p>Loading...</p>;
  }

  return (
    <div className="container mx-auto">
      <div className="flex items-center justify-center gap-4 my-4 max-w-3xl mx-auto">
        <Slider value={currentMessageIndex} setValue={setCurrentMessageIndex} />
        <button
          className="bg-blue-500 text-white w-[80px] rounded-md px-4 py-2"
          onClick={() => setPlay((prev) => !prev)}
        >
          {play ? "Stop" : "Start"}
        </button>
      </div>
      <canvas ref={canvasRef} />
    </div>
  );
};
