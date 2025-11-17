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
      case EMessageType.EBGenerated:
      case EMessageType.RBGenerated:
      case EMessageType.VTBundleGenerated:
      case EMessageType.TransactionGenerated: {
        const nodeId = 'producer' in message ? message.producer : message.publisher;
        const stats = nodeStats.get(nodeId);
        if (stats) {
          stats.generated[message.type] = (stats.generated[message.type] || 0) + 1;
        }
        break;
      }
      
      case EMessageType.EBSent:
      case EMessageType.RBSent:
      case EMessageType.VTBundleSent:
      case EMessageType.TransactionSent: {
        const stats = nodeStats.get(message.sender);
        if (stats) {
          if (!stats.sent[message.type]) {
            stats.sent[message.type] = { count: 0, bytes: 0 };
          }
          stats.sent[message.type].count += 1;
        }
        break;
      }
      
      case EMessageType.EBReceived:
      case EMessageType.RBReceived:
      case EMessageType.VTBundleReceived:
      case EMessageType.TransactionReceived: {
        const stats = nodeStats.get(message.recipient);
        if (stats) {
          if (!stats.received[message.type]) {
            stats.received[message.type] = { count: 0, bytes: 0 };
          }
          stats.received[message.type].count += 1;
        }
        break;
      }
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