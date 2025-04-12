/** Rust simulation trace format */

import * as shared from "./trace.shared";

interface RustTraceEvent {
    time_s: number;
    message: RustEvent
}

type RustEvent =
    | CpuEvent
    | BlockEvent
    | NetworkEvent
    | SlotEvent;

type CpuEvent =
    | CpuSubtaskEvent
    | ScheduledCpuTaskEvent
    | CpuTaskFinishedEvent;

interface CpuSubtaskEvent {
    type: "Cpu";
    node: string;
    cpu_time_s: number;
    task_label: string;
    task_type: CpuTaskType;
    id: string;
}

interface ScheduledCpuTaskEvent {
    type: "CpuTaskScheduled";
    task_type: CpuTaskType;
    subtasks: number;
}

interface CpuTaskFinishedEvent {
    type: "CpuTaskFinished";
    task_type: CpuTaskType;
    cpu_time_s: number;
}

type CpuTaskType = shared.CpuTaskType;

type BlockEvent = shared.BlockEvent | LotteryWon | GeneratedTransaction;

interface LotteryWon {
    type: "IBLotteryWon" | "EBLotteryWon" | "VTLotteryWon";
    id: string;
    slot: number;
    producer: string;
}

interface GeneratedTransaction {
    type: "TXGenerated";
    id: string;
    publisher: string;
    size_bytes: number;
}

interface NetworkEvent extends Omit<shared.NetworkEvent, "type"> {
    type: NetworkEventType
}

type NetworkEventType = shared.NetworkEventType | "TXSent" | "TXReceived";

interface SlotEvent {
    type: "GlobalSlot";
    slot: number;
}

// Type to validate `jq '.' -cs` of a log.
type TraceEvents = RustTraceEvent[]

type KnownType = RustEvent["type"];
