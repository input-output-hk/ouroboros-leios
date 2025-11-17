import { useMemo } from "react";
import { useSimContext } from "@/contexts/SimContext/context";
import {
  computeAggregatedDataAtTime,
  getEventCountsAtTime,
} from "@/utils/timelineAggregation";

/**
 * Hook that provides on-demand aggregated data based on current timeline time
 */
export const useTimelineAggregation = () => {
  const { state } = useSimContext();
  const { events, currentTime, topography } = state;

  // Get all node IDs from topology
  const nodeIds = useMemo(() => {
    return Array.from(topography.nodes.keys());
  }, [topography.nodes]);

  // Compute aggregated data at current timeline time
  const aggregatedStats = useMemo(() => {
    if (events.length === 0) {
      return new Map();
    }

    return computeAggregatedDataAtTime(events, currentTime, nodeIds);
  }, [events, currentTime, nodeIds]);

  // Simple event counts for debugging
  const eventCounts = useMemo(() => {
    return getEventCountsAtTime(events, currentTime);
  }, [events, currentTime]);

  return {
    aggregatedStats,
    eventCounts,
    totalEvents: events.length,
    currentTime: currentTime,
  };
};
