import { useCallback, useMemo } from "react";
import {
  ReactFlow,
  Background,
  type Node,
  type Edge,
  type NodeChange,
  type NodeMouseHandler,
  type EdgeMouseHandler,
} from "@xyflow/react";
import "@xyflow/react/dist/style.css";
import { useStore } from "@/store";
import { TopologyNode } from "./TopologyNode";
import { TopologyEdge } from "./TopologyEdge";

const nodeTypes = { topologyNode: TopologyNode };
const edgeTypes = { topologyEdge: TopologyEdge };

export function TopologyGraph() {
  const topology = useStore((s) => s.topology);
  const nodePositions = useStore((s) => s.nodePositions);
  const selectedNodeId = useStore((s) => s.selectedNodeId);
  const selectedEdge = useStore((s) => s.selectedEdge);
  const nodeFlash = useStore((s) => s.nodeFlash);
  const selectNode = useStore((s) => s.selectNode);
  const selectEdge = useStore((s) => s.selectEdge);
  const setNodePosition = useStore((s) => s.setNodePosition);

  const nodes: Node[] = useMemo(() => {
    if (!topology) return [];
    return topology.nodes.map((n) => ({
      id: n.node_id,
      position: nodePositions[n.node_id] ?? { x: 0, y: 0 },
      type: "topologyNode",
      data: {
        label: n.node_id,
        stake: n.stake,
        selected: selectedNodeId === n.node_id,
        flash: nodeFlash[n.node_id] ?? null,
      },
    }));
  }, [topology, nodePositions, selectedNodeId, nodeFlash]);

  const edges: Edge[] = useMemo(() => {
    if (!topology) return [];
    return topology.edges.map((e) => {
      const sourceId = topology.nodes[e.from]?.node_id ?? "";
      const targetId = topology.nodes[e.to]?.node_id ?? "";
      return {
        id: `${e.from}-${e.to}`,
        source: sourceId,
        target: targetId,
        type: "topologyEdge",
        data: {
          latency_ms: e.latency_ms,
          selected:
            selectedEdge?.from === e.from && selectedEdge?.to === e.to,
        },
      };
    });
  }, [topology, selectedEdge]);

  const onNodesChange = useCallback(
    (changes: NodeChange[]) => {
      for (const change of changes) {
        if (change.type === "position" && change.dragging && change.position && change.id) {
          setNodePosition(change.id, change.position);
        }
      }
    },
    [setNodePosition],
  );

  const onNodeClick: NodeMouseHandler = useCallback(
    (_event, node) => {
      selectNode(node.id);
    },
    [selectNode, selectedNodeId],
  );

  const onEdgeClick: EdgeMouseHandler = useCallback(
    (_event, edge) => {
      const parts = edge.id.split("-");
      const from = Number(parts[0]);
      const to = Number(parts[1]);
      selectEdge({ from, to });
    },
    [selectEdge, selectedEdge],
  );

  const onPaneClick = useCallback(() => {
    selectNode(null);
    selectEdge(null);
  }, [selectNode, selectEdge]);

  return (
    <ReactFlow
      nodes={nodes}
      edges={edges}
      nodeTypes={nodeTypes}
      edgeTypes={edgeTypes}
      onNodesChange={onNodesChange}
      onNodeClick={onNodeClick}
      onEdgeClick={onEdgeClick}
      onPaneClick={onPaneClick}
      fitView
      minZoom={0.3}
      maxZoom={3}
      proOptions={{ hideAttribution: true }}
    >
      <Background color="#333" gap={20} />
    </ReactFlow>
  );
}
