import { IServerMessage, EMessageType } from '@/components/Sim/types';
import { ISimulationAggregatedData } from '@/contexts/SimContext/types';

/**
 * Compute aggregated statistics from timeline events up to a specific time
 */
export const computeAggregatedDataAtTime = (
  events: IServerMessage[],
  targetTime: number,
  nodeIds: string[]
): Map<string, ISimulationAggregatedData> => {
  const nodeStats = new Map<string, ISimulationAggregatedData>();
  
  // Initialize stats for all nodes
  nodeIds.forEach(nodeId => {
    nodeStats.set(nodeId, {
      bytesSent: 0,
      bytesReceived: 0,
      generated: {},
      sent: {},
      received: {},
    });
  });
  
  // Process events up to target time
  const filteredEvents = events.filter(event => event.time_s <= targetTime);
  
  for (const event of filteredEvents) {
    const { message } = event;
    
    switch (message.type) {
      case EMessageType.EBGenerated: {
        const stats = nodeStats.get(message.producer);
        if (stats) {
          stats.generated[message.type] = (stats.generated[message.type] || 0) + 1;
        }
        break;
      }
      
      case EMessageType.EBSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          if (!stats.sent[message.type]) {
            stats.sent[message.type] = { count: 0, bytes: 0 };
          }
          stats.sent[message.type].count += 1;
          // Note: EBSent doesn't have size_bytes, we'd need to track from EBGenerated
        }
        break;
      }
      
      case EMessageType.EBReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          if (!stats.received[message.type]) {
            stats.received[message.type] = { count: 0, bytes: 0 };
          }
          stats.received[message.type].count += 1;
          // Note: EBReceived doesn't have size_bytes, we'd need to track from EBGenerated
        }
        break;
      }
      
      // Add other message types as needed
    }
  }
  
  return nodeStats;
};

/**
 * Get simple counts for debugging timeline functionality
 */
export const getEventCountsAtTime = (
  events: IServerMessage[],
  targetTime: number
): { total: number; byType: Record<string, number> } => {
  const filteredEvents = events.filter(event => event.time_s <= targetTime);
  const byType: Record<string, number> = {};
  
  for (const event of filteredEvents) {
    const type = event.message.type;
    byType[type] = (byType[type] || 0) + 1;
  }
  
  return {
    total: filteredEvents.length,
    byType,
  };
};