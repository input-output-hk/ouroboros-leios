import { useRef, useEffect, useCallback, useState } from 'react';
import type { VisualNode, VisualEdge, AnimatedTx, LayoutType } from '@/simulation';

export interface SelectedNodeInfo {
  id: string;
  honest: boolean;
  upstream: string[];   // nodes that send TO this node
  downstream: string[]; // nodes this node sends TO
}

interface CanvasProps {
  nodes: VisualNode[];
  edges: VisualEdge[];
  animatedTxs: AnimatedTx[];
  blockFlash: { nodeId: string; opacity: number } | null;
  blockCount: number;
  selectedNode: SelectedNodeInfo | null;
  onNodeSelect: (node: SelectedNodeInfo | null) => void;
  onDragStart?: (nodeId: string, x: number, y: number) => void;
  onDrag?: (nodeId: string, x: number, y: number) => void;
  onDragEnd?: (nodeId: string) => void;
  layoutType: LayoutType;
  zoom: number;
  onZoomChange: (zoom: number) => void;
}

// Theme colors from Leios site
const COLORS = {
  background: '#180425',
  border: '#45364e',
  text: '#f8f6fa',
  textMuted: '#8f6dae',
  honest: '#6effd1',       // teal/mint accent
  honestDim: '#2a5a4d',
  adversary: '#ef4444',    // red
  adversaryDim: '#5c2020',
  frontrun: '#f97316',     // orange for front-run tx
  edgeNormal: '#45364e',
  edgeDim: '#2d1f38',
  edgeHighlight: '#8f6dae',
  selection: '#ffffff',
  blockFlash: 'rgba(110, 255, 209, 0.5)',
  poisoned: '#f97316',  // orange - matches frontrun tx color
};

export function Canvas({
  nodes,
  edges,
  animatedTxs,
  blockFlash,
  blockCount,
  selectedNode,
  onNodeSelect,
  onDragStart,
  onDrag,
  onDragEnd,
  layoutType,
  zoom,
  onZoomChange,
}: CanvasProps) {
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const nodePositions = useRef<Map<string, { x: number; y: number }>>(new Map());
  const [size, setSize] = useState({ width: 800, height: 600 });
  const [offset, setOffset] = useState({ x: 0, y: 0 });
  const [panOffset, setPanOffset] = useState({ x: 0, y: 0 });
  const [isPanning, setIsPanning] = useState(false);
  const [draggingNode, setDraggingNode] = useState<string | null>(null);
  const [hoveredNode, setHoveredNode] = useState<string | null>(null);
  const hoveredNodeRef = useRef<string | null>(null);
  const panStartRef = useRef({ x: 0, y: 0, panX: 0, panY: 0 });
  const dragStartRef = useRef({ x: 0, y: 0 });

  // Resize observer to fill viewport
  useEffect(() => {
    const updateSize = () => {
      setSize({ width: window.innerWidth, height: window.innerHeight });
    };

    updateSize();
    window.addEventListener('resize', updateSize);
    return () => window.removeEventListener('resize', updateSize);
  }, []);

  useEffect(() => {
    // Calculate graph dimensions based on smaller viewport dimension
    const graphSize = Math.min(size.width, size.height) * 0.85 * zoom;
    const scale = graphSize / 640; // base size was 640

    // Center the graph (before zoom)
    const offsetX = (size.width - graphSize) / 2;
    const offsetY = (size.height - graphSize) / 2;
    setOffset({ x: offsetX, y: offsetY });

    nodes.forEach(node => {
      nodePositions.current.set(node.id, {
        x: node.position.x * scale + offsetX + panOffset.x,
        y: node.position.y * scale + offsetY + panOffset.y,
      });
    });
  }, [nodes, size, panOffset, zoom]);

  // Find node at a given position
  const findNodeAtPosition = useCallback((x: number, y: number): VisualNode | undefined => {
    const graphSize = Math.min(size.width, size.height) * 0.85 * zoom;
    const scale = graphSize / 640;

    return nodes.find(node => {
      const pos = nodePositions.current.get(node.id);
      if (!pos) return false;
      const dx = pos.x - x;
      const dy = pos.y - y;
      const distance = Math.sqrt(dx * dx + dy * dy);
      return distance <= 14 * scale;
    });
  }, [nodes, size, zoom]);

  const handleMouseDown = useCallback((e: React.MouseEvent<HTMLCanvasElement>) => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    // Check if clicking on a node (for force layout dragging)
    const clickedNode = findNodeAtPosition(x, y);

    if (clickedNode && layoutType === 'force' && onDragStart) {
      setDraggingNode(clickedNode.id);
      dragStartRef.current = { x, y };
      onDragStart(clickedNode.id, clickedNode.position.x, clickedNode.position.y);
    } else {
      // Start panning
      setIsPanning(true);
      panStartRef.current = { x: e.clientX, y: e.clientY, panX: panOffset.x, panY: panOffset.y };
    }
  }, [findNodeAtPosition, layoutType, onDragStart, panOffset]);

  const handleMouseMove = useCallback((e: React.MouseEvent<HTMLCanvasElement>) => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    if (draggingNode && onDrag) {
      // Convert screen coords back to sim coords
      const graphSize = Math.min(size.width, size.height) * 0.85 * zoom;
      const scale = graphSize / 640;
      const simX = (x - offset.x - panOffset.x) / scale;
      const simY = (y - offset.y - panOffset.y) / scale;

      onDrag(draggingNode, simX, simY);
    } else if (isPanning) {
      const dx = e.clientX - panStartRef.current.x;
      const dy = e.clientY - panStartRef.current.y;
      setPanOffset({ x: panStartRef.current.panX + dx, y: panStartRef.current.panY + dy });
    } else {
      // Update hover state - use ref to avoid draw recreation, state for cursor
      const node = findNodeAtPosition(x, y);
      const newHoveredId = node?.id ?? null;
      hoveredNodeRef.current = newHoveredId;
      setHoveredNode(newHoveredId);
    }
  }, [draggingNode, isPanning, onDrag, offset, panOffset, size, zoom, findNodeAtPosition]);

  const handleMouseUp = useCallback((e: React.MouseEvent<HTMLCanvasElement>) => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    // If we were dragging, check if it was just a click (minimal movement)
    if (draggingNode) {
      const dx = x - dragStartRef.current.x;
      const dy = y - dragStartRef.current.y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (onDragEnd) onDragEnd(draggingNode);
      setDraggingNode(null);

      // If moved more than a few pixels, it was a drag - don't select
      if (distance > 5) return;

      // It was a click - select the node
      const clickedNode = findNodeAtPosition(x, y);
      if (clickedNode) {
        const upstream = edges.filter(e => e.target === clickedNode.id).map(e => e.source);
        const downstream = edges.filter(e => e.source === clickedNode.id).map(e => e.target);
        onNodeSelect({
          id: clickedNode.id,
          honest: clickedNode.honest,
          upstream,
          downstream,
        });
      }
      return;
    }

    // If we were panning, check if it was just a click (minimal movement)
    if (isPanning) {
      setIsPanning(false);
      const dx = e.clientX - panStartRef.current.x;
      const dy = e.clientY - panStartRef.current.y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      // If moved more than a few pixels, it was a pan - don't select
      if (distance > 5) return;
    }

    // Handle click/selection
    const clickedNode = findNodeAtPosition(x, y);

    if (clickedNode) {
      const upstream = edges.filter(e => e.target === clickedNode.id).map(e => e.source);
      const downstream = edges.filter(e => e.source === clickedNode.id).map(e => e.target);

      onNodeSelect({
        id: clickedNode.id,
        honest: clickedNode.honest,
        upstream,
        downstream,
      });
    } else {
      onNodeSelect(null);
    }
  }, [draggingNode, isPanning, findNodeAtPosition, edges, onNodeSelect, onDragEnd]);

  const handleMouseLeave = useCallback(() => {
    if (isPanning) setIsPanning(false);
    if (draggingNode) {
      if (onDragEnd) onDragEnd(draggingNode);
      setDraggingNode(null);
    }
    hoveredNodeRef.current = null;
    setHoveredNode(null);
  }, [isPanning, draggingNode, onDragEnd]);

  const handleDoubleClick = useCallback(() => {
    // Reset pan and zoom
    setPanOffset({ x: 0, y: 0 });
    onZoomChange(1);
  }, [onZoomChange]);

  // Mouse wheel zoom
  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const handleWheel = (e: WheelEvent) => {
      e.preventDefault();
      const delta = e.deltaY > 0 ? -0.1 : 0.1;
      const newZoom = Math.max(0.5, Math.min(3, zoom + delta));
      onZoomChange(newZoom);
    };

    canvas.addEventListener('wheel', handleWheel, { passive: false });
    return () => canvas.removeEventListener('wheel', handleWheel);
  }, [zoom, onZoomChange]);

  const draw = useCallback(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;

    const ctx = canvas.getContext('2d');
    if (!ctx) return;

    const { width, height } = size;
    const graphSize = Math.min(width, height) * 0.85 * zoom;
    const scale = graphSize / 640;

    // Clear canvas
    ctx.fillStyle = COLORS.background;
    ctx.fillRect(0, 0, width, height);

    // Draw edges
    edges.forEach(edge => {
      const fromPos = nodePositions.current.get(edge.source);
      const toPos = nodePositions.current.get(edge.target);
      if (fromPos && toPos) {
        // Highlight edges connected to selected node
        let edgeColor = COLORS.edgeNormal;
        let lineWidth = 1;

        if (selectedNode) {
          if (edge.target === selectedNode.id) {
            // Upstream edge (pointing TO selected node)
            edgeColor = COLORS.edgeHighlight;
            lineWidth = 2;
          } else if (edge.source === selectedNode.id) {
            // Downstream edge (FROM selected node)
            edgeColor = COLORS.textMuted;
            lineWidth = 2;
          } else {
            edgeColor = COLORS.edgeDim;
          }
        }

        ctx.strokeStyle = edgeColor;
        ctx.lineWidth = lineWidth * scale;
        ctx.beginPath();
        ctx.moveTo(fromPos.x, fromPos.y);
        ctx.lineTo(toPos.x, toPos.y);
        ctx.stroke();

        // Draw arrowhead for highlighted edges
        if (selectedNode && (edge.target === selectedNode.id || edge.source === selectedNode.id)) {
          const angle = Math.atan2(toPos.y - fromPos.y, toPos.x - fromPos.x);
          const arrowLen = 10 * scale;
          const arrowX = toPos.x - 12 * scale * Math.cos(angle);
          const arrowY = toPos.y - 12 * scale * Math.sin(angle);

          ctx.beginPath();
          ctx.moveTo(arrowX, arrowY);
          ctx.lineTo(
            arrowX - arrowLen * Math.cos(angle - Math.PI / 6),
            arrowY - arrowLen * Math.sin(angle - Math.PI / 6)
          );
          ctx.lineTo(
            arrowX - arrowLen * Math.cos(angle + Math.PI / 6),
            arrowY - arrowLen * Math.sin(angle + Math.PI / 6)
          );
          ctx.closePath();
          ctx.fillStyle = edgeColor;
          ctx.fill();
        }
      }
    });

    // Draw animated transactions
    animatedTxs.forEach(tx => {
      const fromPos = nodePositions.current.get(tx.fromNode);
      const toPos = nodePositions.current.get(tx.toNode);
      if (fromPos && toPos) {
        const x = fromPos.x + (toPos.x - fromPos.x) * tx.progress;
        const y = fromPos.y + (toPos.y - fromPos.y) * tx.progress;

        // Check if tx is on a connection of the selected/hovered node
        const focusNode = selectedNode?.id ?? hoveredNodeRef.current;
        let isRelevant = true;
        if (focusNode) {
          // Tx is relevant if it involves the focus node or travels on its edges
          const focusUpstream = selectedNode?.upstream ?? [];
          const focusDownstream = selectedNode?.downstream ?? [];
          const isDirectlyConnected =
            tx.fromNode === focusNode ||
            tx.toNode === focusNode;
          const isOnFocusEdge =
            (tx.fromNode === focusNode && focusDownstream.includes(tx.toNode)) ||
            (tx.toNode === focusNode && focusUpstream.includes(tx.fromNode));
          isRelevant = isDirectlyConnected || isOnFocusEdge;
        }

        // Relevant txs are normal size, others are smaller and faded
        const txRadius = isRelevant ? 4 * scale : 2 * scale;
        ctx.beginPath();
        ctx.arc(x, y, txRadius, 0, 2 * Math.PI);
        if (isRelevant) {
          ctx.fillStyle = tx.isAdversarial ? COLORS.frontrun : COLORS.honest;
        } else {
          ctx.fillStyle = tx.isAdversarial ? 'rgba(249, 115, 22, 0.15)' : 'rgba(110, 255, 209, 0.15)';
        }
        ctx.fill();
      }
    });

    // Draw nodes
    nodes.forEach(node => {
      const pos = nodePositions.current.get(node.id);
      if (!pos) return;
      const { x, y } = pos;
      const baseRadius = 8 * scale;
      const fillBonus = (node.mempoolFillPercent / 100) * 6 * scale;
      const radius = baseRadius + fillBonus;

      // Check if this node is related to selection
      const isSelected = selectedNode?.id === node.id;
      const isUpstream = selectedNode?.upstream.includes(node.id);
      const isDownstream = selectedNode?.downstream.includes(node.id);
      const isRelated = isSelected || isUpstream || isDownstream;

      // Dim unrelated nodes when something is selected
      const dimmed = selectedNode && !isRelated;

      // Draw glow for nodes with high mempool fill
      if (node.mempoolFillPercent > 50 && !dimmed) {
        const gradient = ctx.createRadialGradient(x, y, radius, x, y, radius * 2);
        const glowColor = node.honest ? 'rgba(110, 255, 209, 0.3)' : 'rgba(239, 68, 68, 0.3)';
        gradient.addColorStop(0, glowColor);
        gradient.addColorStop(1, 'transparent');
        ctx.beginPath();
        ctx.arc(x, y, radius * 2, 0, 2 * Math.PI);
        ctx.fillStyle = gradient;
        ctx.fill();
      }

      // Block production flash with fade
      if (blockFlash?.nodeId === node.id) {
        const opacity = blockFlash.opacity;
        ctx.beginPath();
        ctx.arc(x, y, radius * 3, 0, 2 * Math.PI);
        ctx.fillStyle = `rgba(110, 255, 209, ${0.5 * opacity})`;
        ctx.fill();

        // "Block #N" label
        ctx.font = `bold ${12 * scale}px monospace`;
        ctx.fillStyle = `rgba(110, 255, 209, ${opacity})`;
        ctx.textAlign = 'left';
        ctx.textBaseline = 'middle';
        ctx.fillText(`Block #${blockCount}`, x + radius * 3 + 4 * scale, y);
      }

      // Hover glow
      const isHovered = hoveredNodeRef.current === node.id;
      if (isHovered && !dimmed) {
        const gradient = ctx.createRadialGradient(x, y, radius, x, y, radius * 2.5);
        gradient.addColorStop(0, 'rgba(255, 255, 255, 0.4)');
        gradient.addColorStop(1, 'transparent');
        ctx.beginPath();
        ctx.arc(x, y, radius * 2.5, 0, 2 * Math.PI);
        ctx.fillStyle = gradient;
        ctx.fill();
      }

      // Poisoned ring (honest nodes with adversarial txs in mempool)
      if (node.honest && node.isPoisoned && !dimmed) {
        ctx.beginPath();
        ctx.arc(x, y, radius + 8 * scale, 0, 2 * Math.PI);
        ctx.strokeStyle = COLORS.poisoned;
        ctx.lineWidth = 3 * scale;
        ctx.stroke();
      }

      // Selection ring
      if (isSelected) {
        ctx.beginPath();
        ctx.arc(x, y, radius + 6 * scale, 0, 2 * Math.PI);
        ctx.strokeStyle = COLORS.selection;
        ctx.lineWidth = 3 * scale;
        ctx.stroke();
      } else if (isUpstream) {
        // Ring for upstream peers
        ctx.beginPath();
        ctx.arc(x, y, radius + 4 * scale, 0, 2 * Math.PI);
        ctx.strokeStyle = COLORS.edgeHighlight;
        ctx.lineWidth = 2 * scale;
        ctx.stroke();
      } else if (isDownstream) {
        // Ring for downstream peers
        ctx.beginPath();
        ctx.arc(x, y, radius + 4 * scale, 0, 2 * Math.PI);
        ctx.strokeStyle = COLORS.textMuted;
        ctx.lineWidth = 2 * scale;
        ctx.stroke();
      } else if (isHovered && !dimmed) {
        // Hover ring
        ctx.beginPath();
        ctx.arc(x, y, radius + 4 * scale, 0, 2 * Math.PI);
        ctx.strokeStyle = 'rgba(255, 255, 255, 0.6)';
        ctx.lineWidth = 2 * scale;
        ctx.stroke();
      }

      // Node circle
      ctx.beginPath();
      ctx.arc(x, y, radius, 0, 2 * Math.PI);
      if (dimmed) {
        ctx.fillStyle = node.honest ? COLORS.honestDim : COLORS.adversaryDim;
      } else {
        ctx.fillStyle = node.honest ? COLORS.honest : COLORS.adversary;
      }
      ctx.fill();

      // Node border based on fill level
      if (dimmed) {
        ctx.strokeStyle = COLORS.edgeNormal;
      } else {
        ctx.strokeStyle = node.honest ? '#a7ffe8' : '#f87171';
      }
      ctx.lineWidth = 2 * scale;
      ctx.stroke();

      // Node label
      ctx.fillStyle = dimmed ? COLORS.edgeHighlight : COLORS.text;
      ctx.font = `${10 * scale}px monospace`;
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(node.id, x, y + radius + 12 * scale);
    });
  }, [nodes, edges, animatedTxs, blockFlash, blockCount, selectedNode, size, offset, zoom]);

  useEffect(() => {
    let frameId: number;
    const animate = () => {
      draw();
      frameId = requestAnimationFrame(animate);
    };
    frameId = requestAnimationFrame(animate);
    return () => cancelAnimationFrame(frameId);
  }, [draw]);

  const getCursor = () => {
    if (isPanning) return 'grabbing';
    if (draggingNode) return 'grabbing';
    if (hoveredNode) return 'pointer';
    return 'grab';
  };

  return (
    <canvas
      ref={canvasRef}
      width={size.width}
      height={size.height}
      onMouseDown={handleMouseDown}
      onMouseMove={handleMouseMove}
      onMouseUp={handleMouseUp}
      onMouseLeave={handleMouseLeave}
      onDoubleClick={handleDoubleClick}
      className="absolute inset-0"
      style={{ cursor: getCursor() }}
    />
  );
}
