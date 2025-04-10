/** Rust simulation trace format */

// Base types
interface RustBaseEvent {
    time_s: number;
    message: {
        type: string;
        [key: string]: any;
    };
}

interface RustTaskInfo {
    node: string;
    index: number;
}

// CPU Events
type BlockOrTaskType =
    | "RBBlock"
    | "EBBlock"
    | "VTBundle"
    | "IBBlock"
    | "IBHeader"
    | "Transaction";
type Action = "Validated" | "Generated";
type RustCpuTaskType = `${BlockOrTaskType}${Action}`;

type CpuTaskPrefix = "CpuTask" | "CpuSubtask";
type CpuTaskAction = "Scheduled" | "Started" | "Finished";
type RustCpuMessageType = `${CpuTaskPrefix}${CpuTaskAction}`;

interface RustCpuEvent extends Omit<RustBaseEvent, "message"> {
    message: {
        type: RustCpuMessageType;
        task: RustTaskInfo;
        task_type?: RustCpuTaskType;
        subtasks?: number;
        subtask_id?: number;
        duration_s?: number;
        cpu_time_s?: number;
        wall_time_s?: number;
        extra?: string;
    };
}

// Block Events
interface RustBaseBlockEvent {
    id: string;
    slot: number;
    pipeline?: number;
    producer: string;
    sender?: string;
    recipient?: string;
}

type BlockType = "IB" | "EB" | "RB";
type BlockAction = "Sent" | "Received" | "LotteryWon" | "Generated";
type RustBlockMessageType = `${BlockType}${BlockAction}`;

interface RustBlockEvent extends Omit<RustBaseEvent, "message"> {
    message: RustBaseBlockEvent & {
        type: RustBlockMessageType;
        index?: number;
        header_bytes?: number;
        size_bytes?: number;
        transactions?: string[];
        vrf?: number;
        endorsement?: any;
        parent?: {
            id: string;
            slot: number;
            producer: string;
        };
    };
}

// Transaction Events
type TransactionAction = "Sent" | "Received" | "Generated";
type RustTransactionMessageType = `Transaction${TransactionAction}`;

interface RustTransactionEvent extends Omit<RustBaseEvent, "message"> {
    message: {
        type: RustTransactionMessageType;
        id: string;
        sender?: string;
        recipient?: string;
        publisher?: string;
        bytes?: number;
    };
}

// Vote Events
type VoteAction = "Received" | "Sent" | "Generated" | "LotteryWon";
type RustVoteMessageType = `Votes${VoteAction}`;

interface RustVoteEvent extends Omit<RustBaseEvent, "message"> {
    message: {
        type: RustVoteMessageType;
        id: string;
        slot: number;
        producer: string;
        sender?: string;
        recipient?: string;
        votes?: Record<string, number>;
    };
}

// Slot Event
interface RustSlotEvent extends Omit<RustBaseEvent, "message"> {
    message: {
        type: "Slot";
        number: number;
    };
}

// Combined type
export type RustTraceEvent =
    | RustCpuEvent
    | RustBlockEvent
    | RustTransactionEvent
    | RustVoteEvent
    | RustSlotEvent;

// Type to validate `jq '.' -cs` of a log.
type TraceEvents = RustTraceEvent[]