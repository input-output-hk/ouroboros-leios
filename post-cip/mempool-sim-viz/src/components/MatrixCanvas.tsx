import { useRef, useEffect, useCallback, useState } from 'react';
import type { Simulation } from 'mempool-sim-web';

const COLORS = {
  background: [0x18, 0x04, 0x25] as const,
  downstream: [0x6e, 0xff, 0xd1] as const,  // teal
  upstream: [0xfb, 0xbf, 0x24] as const,    // amber
  bidirectional: [0xe8, 0x5d, 0xf5] as const,  // magenta
  adversarySep: [0xef, 0x44, 0x44] as const,
  selected: [0x8f, 0x6d, 0xae] as const,
  blockFlashRB: [0xfb, 0xbf, 0x24] as const,
  blockFlashEB: [0x22, 0xd3, 0xee] as const,
  poisoned: [0xef, 0x44, 0x44] as const,
  healthy: [0x6e, 0xff, 0xd1] as const,
};

// Panel width + margin on each side
const PANEL_INSET = 256;
// Margin between panels and matrix
const MATRIX_MARGIN = 16;

// Discrete zoom levels: pixels per cell
export const ZOOM_LEVELS = [1, 2, 3, 5, 7, 10] as const;

interface MatrixCanvasProps {
  sim: Simulation | null;
  nodeOrder: number[];
  honestCount: number;
  blockFlash: { nodeId: string; opacity: number } | null;
  selectedNodeIdx: number | null;
  onNodeSelect: (nodeIdx: number | null) => void;
  width: number;
  height: number;
  zoomIdx: number;
  onZoomIdxChange: (idx: number) => void;
  onRegisterFitView?: (fn: () => void) => void;
}

export function MatrixCanvas({
  sim,
  nodeOrder,
  honestCount,
  blockFlash,
  selectedNodeIdx,
  onNodeSelect,
  width,
  height,
  zoomIdx,
  onZoomIdxChange,
  onRegisterFitView,
}: MatrixCanvasProps) {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const cellSize = ZOOM_LEVELS[zoomIdx]!;
  const [panX, setPanX] = useState(0);
  const [panY, setPanY] = useState(0);
  const isDraggingRef = useRef(false);
  const lastMouseRef = useRef({ x: 0, y: 0 });
  const animFrameRef = useRef<number | null>(null);
  const tooltipRef = useRef<{ x: number; y: number; text: string } | null>(null);

  // Compute available space for the matrix (between side panels)
  const availW = Math.max(200, width - PANEL_INSET * 2 - MATRIX_MARGIN * 2);
  const availH = Math.max(200, height - MATRIX_MARGIN * 2 - 80); // 80 for timeline
  const availPx = Math.min(availW, availH);

  // Binning: when N > availPx, group nodes into bins
  const n = nodeOrder.length;
  const binSize = n > availPx ? Math.ceil(n / availPx) : 1;
  const binCount = binSize > 1 ? Math.ceil(n / binSize) : n;
  const isBinned = binSize > 1;

  // Map from nodeOrder position to node index for reverse lookup
  const orderToPos = useRef<Map<number, number>>(new Map());
  useEffect(() => {
    const map = new Map<number, number>();
    nodeOrder.forEach((nodeIdx, pos) => map.set(nodeIdx, pos));
    orderToPos.current = map;
  }, [nodeOrder]);

  // For binned mode: adversary separator bin position
  const advSepBin = isBinned ? Math.floor(honestCount / binSize) : honestCount;

  // Helper: get nodes in a bin
  const getBinNodes = useCallback((bin: number): number[] => {
    const start = bin * binSize;
    const end = Math.min(start + binSize, n);
    const result: number[] = [];
    for (let i = start; i < end; i++) {
      result.push(nodeOrder[i]!);
    }
    return result;
  }, [nodeOrder, binSize, n]);

  // Render a single cell color for full (unbinned) mode
  const getCellColor = useCallback((row: number, col: number): [number, number, number] => {
    if (!sim) return COLORS.background as unknown as [number, number, number];
    const fromIdx = nodeOrder[row]!;
    const toIdx = nodeOrder[col]!;

    if (row === col) {
      const fill = sim.getNodeFillPercent(fromIdx) / 100;
      const poisoned = sim.isNodePoisoned(fromIdx);
      if (poisoned) {
        return [
          Math.round(COLORS.poisoned[0] * Math.max(0.3, fill)),
          Math.round(COLORS.poisoned[1] * Math.max(0.3, fill) * 0.3),
          Math.round(COLORS.poisoned[2] * Math.max(0.3, fill) * 0.3),
        ];
      }
      return [
        Math.round(COLORS.healthy[0] * Math.max(0.15, fill)),
        Math.round(COLORS.healthy[1] * Math.max(0.15, fill)),
        Math.round(COLORS.healthy[2] * Math.max(0.15, fill)),
      ];
    }

    const hasDown = sim.hasEdge(fromIdx, toIdx);
    const hasUp = sim.hasEdge(toIdx, fromIdx);

    if (hasDown && hasUp) return [...COLORS.bidirectional];
    if (hasDown) return [...COLORS.downstream];
    if (hasUp) return [...COLORS.upstream];
    return [...COLORS.background];
  }, [sim, nodeOrder]);

  // Render the matrix
  const render = useCallback(() => {
    const canvas = canvasRef.current;
    if (!canvas || !sim || nodeOrder.length === 0) return;

    const ctx = canvas.getContext('2d');
    if (!ctx) return;

    const cs = isBinned ? 1 : cellSize;
    const displayN = binCount;

    // Center the matrix in the viewport
    const matrixPx = displayN * cs;
    const centerX = Math.round((width - matrixPx) / 2);
    const centerY = Math.round((height - matrixPx) / 2);
    const effPanX = isBinned ? centerX : panX + centerX;
    const effPanY = isBinned ? centerY : panY + centerY;

    // Compute visible range
    const startCol = Math.max(0, Math.floor(-effPanX / cs));
    const endCol = Math.min(displayN, Math.ceil((width - effPanX) / cs));
    const startRow = Math.max(0, Math.floor(-effPanY / cs));
    const endRow = Math.min(displayN, Math.ceil((height - effPanY) / cs));

    const visW = endCol - startCol;
    const visH = endRow - startRow;

    if (visW <= 0 || visH <= 0) {
      ctx.fillStyle = '#180425';
      ctx.fillRect(0, 0, width, height);
      return;
    }

    // Clear canvas
    ctx.fillStyle = '#180425';
    ctx.fillRect(0, 0, width, height);

    if (isBinned) {
      // --- Binned / density mode ---
      const imgW = visW;
      const imgH = visH;
      const imageData = ctx.createImageData(imgW, imgH);
      const data = imageData.data;

      for (let bRow = startRow; bRow < endRow; bRow++) {
        const rowNodes = getBinNodes(bRow);
        for (let bCol = startCol; bCol < endCol; bCol++) {
          const colNodes = getBinNodes(bCol);

          let r: number, g: number, b: number;

          if (bRow === bCol) {
            // Diagonal bin: average mempool fill, check poisoned
            let fillSum = 0;
            let poisoned = false;
            for (const ni of rowNodes) {
              fillSum += sim.getNodeFillPercent(ni) / 100;
              if (!poisoned && sim.isNodePoisoned(ni)) poisoned = true;
            }
            const avgFill = fillSum / rowNodes.length;
            if (poisoned) {
              r = Math.round(COLORS.poisoned[0] * Math.max(0.3, avgFill));
              g = Math.round(COLORS.poisoned[1] * Math.max(0.3, avgFill) * 0.3);
              b = Math.round(COLORS.poisoned[2] * Math.max(0.3, avgFill) * 0.3);
            } else {
              r = Math.round(COLORS.healthy[0] * Math.max(0.15, avgFill));
              g = Math.round(COLORS.healthy[1] * Math.max(0.15, avgFill));
              b = Math.round(COLORS.healthy[2] * Math.max(0.15, avgFill));
            }
          } else {
            // Count edges between bin groups
            let downCount = 0;
            let upCount = 0;
            for (const ri of rowNodes) {
              for (const ci of colNodes) {
                if (sim.hasEdge(ri, ci)) downCount++;
                if (sim.hasEdge(ci, ri)) upCount++;
              }
            }
            const maxEdges = rowNodes.length * colNodes.length;
            const downDensity = downCount / maxEdges;
            const upDensity = upCount / maxEdges;

            if (downCount > 0 && upCount > 0) {
              // Bidirectional — blend toward white by combined density
              const density = Math.min(1, (downDensity + upDensity) / 2);
              const intensity = Math.max(0.15, density);
              r = Math.round(COLORS.bidirectional[0] * intensity);
              g = Math.round(COLORS.bidirectional[1] * intensity);
              b = Math.round(COLORS.bidirectional[2] * intensity);
            } else if (downCount > 0) {
              const intensity = Math.max(0.15, downDensity);
              r = Math.round(COLORS.downstream[0] * intensity);
              g = Math.round(COLORS.downstream[1] * intensity);
              b = Math.round(COLORS.downstream[2] * intensity);
            } else if (upCount > 0) {
              const intensity = Math.max(0.15, upDensity);
              r = Math.round(COLORS.upstream[0] * intensity);
              g = Math.round(COLORS.upstream[1] * intensity);
              b = Math.round(COLORS.upstream[2] * intensity);
            } else {
              [r, g, b] = COLORS.background;
            }
          }

          const idx = ((bRow - startRow) * imgW + (bCol - startCol)) * 4;
          data[idx] = r;
          data[idx + 1] = g;
          data[idx + 2] = b;
          data[idx + 3] = 255;
        }
      }

      const drawX = effPanX + startCol;
      const drawY = effPanY + startRow;
      ctx.putImageData(imageData, drawX, drawY);

      // Adversary separator line in binned mode
      if (honestCount > 0 && honestCount < n) {
        ctx.strokeStyle = `rgba(${COLORS.adversarySep.join(',')}, 0.6)`;
        ctx.lineWidth = 1;
        const sepPixel = advSepBin;
        ctx.beginPath();
        ctx.moveTo(effPanX, effPanY + sepPixel);
        ctx.lineTo(effPanX + binCount, effPanY + sepPixel);
        ctx.stroke();
        ctx.beginPath();
        ctx.moveTo(effPanX + sepPixel, effPanY);
        ctx.lineTo(effPanX + sepPixel, effPanY + binCount);
        ctx.stroke();
      }

      // Binned mode label
      ctx.font = '10px monospace';
      ctx.fillStyle = 'rgba(143, 109, 174, 0.7)';
      ctx.fillText(
        `${n.toLocaleString()} nodes · ${binSize} per px · ${binCount}×${binCount} px`,
        effPanX, effPanY + binCount + 14,
      );
    } else {
      // --- Full (unbinned) mode ---
      if (cs >= 2) {
        const imgW = visW * cs;
        const imgH = visH * cs;
        const imageData = ctx.createImageData(imgW, imgH);
        const data = imageData.data;

        for (let row = startRow; row < endRow; row++) {
          for (let col = startCol; col < endCol; col++) {
            const [r, g, b] = getCellColor(row, col);
            const localCol = col - startCol;
            const localRow = row - startRow;
            for (let py = 0; py < cs; py++) {
              for (let px = 0; px < cs; px++) {
                const idx = ((localRow * cs + py) * imgW + localCol * cs + px) * 4;
                data[idx] = r;
                data[idx + 1] = g;
                data[idx + 2] = b;
                data[idx + 3] = 255;
              }
            }
          }
        }

        ctx.putImageData(imageData, effPanX + startCol * cs, effPanY + startRow * cs);
      } else {
        // cellSize === 1
        const imgW = visW;
        const imgH = visH;
        const imageData = ctx.createImageData(imgW, imgH);
        const data = imageData.data;

        for (let row = startRow; row < endRow; row++) {
          for (let col = startCol; col < endCol; col++) {
            const [r, g, b] = getCellColor(row, col);
            const idx = ((row - startRow) * imgW + (col - startCol)) * 4;
            data[idx] = r;
            data[idx + 1] = g;
            data[idx + 2] = b;
            data[idx + 3] = 255;
          }
        }

        ctx.putImageData(imageData, effPanX + startCol, effPanY + startRow);
      }

      // Adversary separator line (full mode)
      if (honestCount > 0 && honestCount < n) {
        const sepPos = honestCount * cs;
        ctx.strokeStyle = `rgba(${COLORS.adversarySep.join(',')}, 0.6)`;
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(effPanX, effPanY + sepPos);
        ctx.lineTo(effPanX + n * cs, effPanY + sepPos);
        ctx.stroke();
        ctx.beginPath();
        ctx.moveTo(effPanX + sepPos, effPanY);
        ctx.lineTo(effPanX + sepPos, effPanY + n * cs);
        ctx.stroke();
      }
    }

    // --- Overlay rendering (both modes) ---

    const effCs = isBinned ? 1 : cs;
    const effN = isBinned ? binCount : n;
    const effOffX = effPanX;
    const effOffY = effPanY;

    // Selected node highlight
    if (selectedNodeIdx !== null) {
      const fullPos = orderToPos.current.get(selectedNodeIdx);
      if (fullPos !== undefined) {
        const displayPos = isBinned ? Math.floor(fullPos / binSize) : fullPos;
        ctx.fillStyle = `rgba(${COLORS.selected.join(',')}, 0.25)`;
        ctx.fillRect(effOffX, effOffY + displayPos * effCs, effN * effCs, effCs);
        ctx.fillRect(effOffX + displayPos * effCs, effOffY, effCs, effN * effCs);
      }
    }

    // Block flash
    if (blockFlash) {
      const nodeList = sim.nodes;
      const flashNode = nodeList.find(nd => nd.id === blockFlash.nodeId);
      if (flashNode) {
        const fullPos = orderToPos.current.get(flashNode.idx);
        if (fullPos !== undefined) {
          const displayPos = isBinned ? Math.floor(fullPos / binSize) : fullPos;
          const alpha = blockFlash.opacity * 0.4;
          ctx.fillStyle = `rgba(${COLORS.blockFlashRB.join(',')}, ${alpha})`;
          ctx.fillRect(effOffX, effOffY + displayPos * effCs, effN * effCs, effCs);
          ctx.fillRect(effOffX + displayPos * effCs, effOffY, effCs, effN * effCs);
        }
      }
    }

    // Axis labels
    ctx.font = '11px sans-serif';
    ctx.fillStyle = 'rgba(143, 109, 174, 0.8)';

    // Top axis: columns = the peer that receives
    ctx.textAlign = 'center';
    ctx.fillText('Peer →', effOffX + (effN * effCs) / 2, effOffY - 6);

    // Left axis: rows = the node that sends
    ctx.save();
    ctx.translate(effOffX - 6, effOffY + (effN * effCs) / 2);
    ctx.rotate(-Math.PI / 2);
    ctx.textAlign = 'center';
    ctx.fillText('Node ↓', 0, 0);
    ctx.restore();

    // Section labels along axes (honest / adversary) when adversaries present
    if (honestCount > 0 && honestCount < n) {
      const sepDisplay = isBinned ? advSepBin : honestCount;
      ctx.font = '9px sans-serif';
      ctx.fillStyle = 'rgba(110, 255, 209, 0.5)';
      // Top: honest section
      ctx.textAlign = 'center';
      ctx.fillText('honest', effOffX + (sepDisplay * effCs) / 2, effOffY - 18);
      // Top: adversary section
      ctx.fillStyle = 'rgba(239, 68, 68, 0.5)';
      ctx.fillText('adversary', effOffX + (sepDisplay + (effN - sepDisplay) / 2) * effCs, effOffY - 18);

      // Left: honest section
      ctx.fillStyle = 'rgba(110, 255, 209, 0.5)';
      ctx.save();
      ctx.translate(effOffX - 18, effOffY + (sepDisplay * effCs) / 2);
      ctx.rotate(-Math.PI / 2);
      ctx.textAlign = 'center';
      ctx.fillText('honest', 0, 0);
      ctx.restore();

      // Left: adversary section
      ctx.fillStyle = 'rgba(239, 68, 68, 0.5)';
      ctx.save();
      ctx.translate(effOffX - 18, effOffY + (sepDisplay + (effN - sepDisplay) / 2) * effCs);
      ctx.rotate(-Math.PI / 2);
      ctx.textAlign = 'center';
      ctx.fillText('adversary', 0, 0);
      ctx.restore();
    }

    // Reset text alignment
    ctx.textAlign = 'left';

    // Tooltip
    if (tooltipRef.current) {
      const tt = tooltipRef.current;
      ctx.font = '11px monospace';
      const metrics = ctx.measureText(tt.text);
      const pad = 4;
      const ttW = metrics.width + pad * 2;
      const ttH = 18;
      const ttX = Math.min(tt.x + 12, width - ttW - 4);
      const ttY = Math.max(tt.y - ttH - 4, 4);
      ctx.fillStyle = 'rgba(32, 8, 48, 0.9)';
      ctx.fillRect(ttX, ttY, ttW, ttH);
      ctx.fillStyle = '#f8f6fa';
      ctx.fillText(tt.text, ttX + pad, ttY + 13);
    }
  }, [sim, nodeOrder, honestCount, cellSize, panX, panY, width, height,
      selectedNodeIdx, blockFlash, isBinned, binSize, binCount, advSepBin,
      n, availW, availH, getCellColor, getBinNodes]);

  // Continuous render loop
  useEffect(() => {
    let running = true;
    const loop = () => {
      if (!running) return;
      render();
      animFrameRef.current = requestAnimationFrame(loop);
    };
    animFrameRef.current = requestAnimationFrame(loop);
    return () => {
      running = false;
      if (animFrameRef.current) cancelAnimationFrame(animFrameRef.current);
    };
  }, [render]);

  // Mouse wheel zoom (only in full mode)
  const handleWheel = useCallback((e: React.WheelEvent) => {
    if (isBinned) return;
    e.preventDefault();
    if (e.deltaY > 0) {
      onZoomIdxChange(Math.max(0, zoomIdx - 1));
    } else {
      onZoomIdxChange(Math.min(ZOOM_LEVELS.length - 1, zoomIdx + 1));
    }
  }, [isBinned, zoomIdx, onZoomIdxChange]);

  // Mouse drag for panning (only in full mode)
  const handleMouseDown = useCallback((e: React.MouseEvent) => {
    if (isBinned) return;
    if (e.button === 0) {
      isDraggingRef.current = true;
      lastMouseRef.current = { x: e.clientX, y: e.clientY };
    }
  }, [isBinned]);

  const handleMouseMove = useCallback((e: React.MouseEvent) => {
    if (isDraggingRef.current && !isBinned) {
      const dx = e.clientX - lastMouseRef.current.x;
      const dy = e.clientY - lastMouseRef.current.y;
      lastMouseRef.current = { x: e.clientX, y: e.clientY };
      setPanX(prev => prev + dx);
      setPanY(prev => prev + dy);
    }

    // Update tooltip
    const canvas = canvasRef.current;
    const rect = canvas?.getBoundingClientRect();
    if (!rect || !canvas || !sim || nodeOrder.length === 0) {
      tooltipRef.current = null;
      return;
    }
    // Scale mouse coords to canvas pixel space (CSS size may differ from buffer size)
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const mx = (e.clientX - rect.left) * scaleX;
    const my = (e.clientY - rect.top) * scaleY;

    const cs = isBinned ? 1 : cellSize;
    const displayN_ = isBinned ? binCount : n;
    const matrixPx_ = displayN_ * cs;
    const cx = Math.round((width - matrixPx_) / 2);
    const cy = Math.round((height - matrixPx_) / 2);
    const offX = isBinned ? cx : panX + cx;
    const offY = isBinned ? cy : panY + cy;

    const col = Math.floor((mx - offX) / cs);
    const row = Math.floor((my - offY) / cs);
    const displayN = isBinned ? binCount : n;

    if (row >= 0 && row < displayN && col >= 0 && col < displayN) {
      if (isBinned) {
        const rowStart = row * binSize;
        const rowEnd = Math.min(rowStart + binSize, n) - 1;
        const colStart = col * binSize;
        const colEnd = Math.min(colStart + binSize, n) - 1;
        const fromNode0 = sim.nodes[nodeOrder[rowStart]!]!;
        const toNode0 = sim.nodes[nodeOrder[colStart]!]!;
        if (binSize === 1) {
          if (row === col) {
            const fill = sim.getNodeFillPercent(nodeOrder[row]!).toFixed(0);
            tooltipRef.current = { x: mx, y: my, text: `${fromNode0.id} (${fill}% full)` };
          } else {
            const fromIdx = nodeOrder[row]!;
            const toIdx = nodeOrder[col]!;
            const hasDown = sim.hasEdge(fromIdx, toIdx);
            const hasUp = sim.hasEdge(toIdx, fromIdx);
            const dir = hasDown && hasUp ? 'bidi' : hasDown ? 'down' : hasUp ? 'up' : 'none';
            tooltipRef.current = { x: mx, y: my, text: `${fromNode0.id} → ${toNode0.id}: ${dir}` };
          }
        } else {
          const fromNodeEnd = sim.nodes[nodeOrder[rowEnd]!]!;
          const toNodeEnd = sim.nodes[nodeOrder[colEnd]!]!;
          tooltipRef.current = {
            x: mx, y: my,
            text: `[${fromNode0.id}..${fromNodeEnd.id}] × [${toNode0.id}..${toNodeEnd.id}]`,
          };
        }
      } else {
        const fromIdx = nodeOrder[row]!;
        const toIdx = nodeOrder[col]!;
        const fromNode = sim.nodes[fromIdx]!;
        const toNode = sim.nodes[toIdx]!;

        if (row === col) {
          const fill = sim.getNodeFillPercent(fromIdx).toFixed(0);
          tooltipRef.current = { x: mx, y: my, text: `${fromNode.id} (${fill}% full)` };
        } else {
          const hasDown = sim.hasEdge(fromIdx, toIdx);
          const hasUp = sim.hasEdge(toIdx, fromIdx);
          const dir = hasDown && hasUp ? 'bidi' : hasDown ? 'down' : hasUp ? 'up' : 'none';
          tooltipRef.current = { x: mx, y: my, text: `${fromNode.id} → ${toNode.id}: ${dir}` };
        }
      }
    } else {
      tooltipRef.current = null;
    }
  }, [sim, nodeOrder, cellSize, panX, panY, width, height, isBinned, binSize, binCount, n]);

  const handleMouseUp = useCallback(() => {
    isDraggingRef.current = false;
  }, []);

  // Click to select node
  const handleClick = useCallback((e: React.MouseEvent) => {
    const canvas = canvasRef.current;
    const rect = canvas?.getBoundingClientRect();
    if (!rect || !canvas || !sim || nodeOrder.length === 0) return;
    const scaleY = canvas.height / rect.height;
    const my = (e.clientY - rect.top) * scaleY;

    const cs = isBinned ? 1 : cellSize;
    const displayN_ = isBinned ? binCount : n;
    const matrixPx_ = displayN_ * cs;
    const cy = Math.round((height - matrixPx_) / 2);
    const offY = isBinned ? cy : panY + cy;
    const row = Math.floor((my - offY) / cs);
    const displayN = displayN_;

    if (row >= 0 && row < displayN) {
      // In binned mode, select the first node in the bin
      const fullRow = isBinned ? row * binSize : row;
      if (fullRow < n) {
        const nodeIdx = nodeOrder[fullRow]!;
        onNodeSelect(selectedNodeIdx === nodeIdx ? null : nodeIdx);
      }
    } else {
      onNodeSelect(null);
    }
  }, [sim, nodeOrder, cellSize, panX, panY, width, height, onNodeSelect, selectedNodeIdx, isBinned, binSize, binCount, n]);

  // Auto-fit on first render or when node count changes (only for unbinned mode)
  const fitView = useCallback(() => {
    if (nodeOrder.length === 0 || isBinned) {
      setPanX(0);
      setPanY(0);
      return;
    }
    const maxCs = Math.floor(Math.min(availW, availH) / n);
    let bestIdx = 0;
    for (let i = ZOOM_LEVELS.length - 1; i >= 0; i--) {
      if (ZOOM_LEVELS[i]! <= maxCs) { bestIdx = i; break; }
    }
    onZoomIdxChange(bestIdx);
    setPanX(0);
    setPanY(0);
  }, [nodeOrder.length, availW, availH, n, isBinned, onZoomIdxChange]);

  useEffect(() => {
    fitView();
  }, [fitView]);

  // Register fitView for external callers
  useEffect(() => {
    if (onRegisterFitView) {
      onRegisterFitView(() => fitView());
    }
  }, [onRegisterFitView, fitView]);

  return (
    <canvas
      ref={canvasRef}
      width={width}
      height={height}
      className="absolute inset-0"
      style={{ cursor: isBinned ? 'default' : isDraggingRef.current ? 'grabbing' : 'crosshair' }}
      onWheel={handleWheel}
      onMouseDown={handleMouseDown}
      onMouseMove={handleMouseMove}
      onMouseUp={handleMouseUp}
      onMouseLeave={handleMouseUp}
      onClick={handleClick}
    />
  );
}
