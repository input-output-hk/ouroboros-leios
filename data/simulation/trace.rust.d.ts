/** Rust simulation trace format */

// Base types
interface BaseEvent {
    time: number; // nanoseconds
}

interface TaskInfo {
    node: string;
    index: number;
}

// CPU Events
type CpuTaskType =
    | "PraosBlockValidated"
    | "EndorserBlockValidated"
    | "VoteBundleValidated"
    | "EndorserBlockGenerated"
    | "VoteBundleGenerated"
    | "InputBlockValidated"
    | "InputBlockGenerated"
    | "TransactionValidated"
    | "PraosBlockGenerated";

interface CpuEvent extends BaseEvent {
    message: {
        type:
            | "CpuTaskScheduled"
            | "CpuTaskFinished"
            | "CpuSubtaskStarted"
            | "CpuSubtaskFinished";
        task: TaskInfo;
        task_type?: CpuTaskType;
        subtasks?: number;
        subtask_id?: number;
        extra?: string;
    };
}

// Block Events
interface BaseBlockEvent {
    id?: string;
    slot: number;
    producer: string;
    sender?: string;
    recipient?: string;
}

interface InputBlockEvent extends BaseEvent {
    message: BaseBlockEvent & {
        type:
            | "InputBlockSent"
            | "InputBlockReceived"
            | "InputBlockLotteryWon"
            | "InputBlockGenerated";
        index: number;
        header_bytes?: number;
        transactions?: string[];
    };
}

interface EndorserBlockEvent extends BaseEvent {
    message: BaseBlockEvent & {
        type:
            | "EndorserBlockSent"
            | "EndorserBlockReceived"
            | "EndorserBlockLotteryWon"
            | "EndorserBlockGenerated";
    };
}

interface PraosBlockEvent extends BaseEvent {
    message: BaseBlockEvent & {
        type:
            | "PraosBlockSent"
            | "PraosBlockReceived"
            | "PraosBlockLotteryWon"
            | "PraosBlockGenerated";
        header_bytes?: number;
        transactions?: string[];
        vrf?: number;
        endorsement?: any;
    };
}

// Transaction Events
interface TransactionEvent extends BaseEvent {
    message: {
        type:
            | "TransactionSent"
            | "TransactionReceived"
            | "TransactionGenerated";
        id: string;
        sender?: string;
        recipient?: string;
        publisher?: string;
        bytes?: number;
    };
}

// Vote Events
interface VoteEvent extends BaseEvent {
    message: {
        type:
            | "VotesReceived"
            | "VotesSent"
            | "VotesGenerated"
            | "VoteLotteryWon";
        id: string;
        slot: number;
        producer: string;
        sender?: string;
        recipient?: string;
        votes?: Record<string, number>;
    };
}

// Slot Event
interface SlotEvent extends BaseEvent {
    message: {
        type: "Slot";
        number: number;
    };
}

// Combined type
export type RustTraceEvent =
    | CpuEvent
    | InputBlockEvent
    | EndorserBlockEvent
    | PraosBlockEvent
    | TransactionEvent
    | VoteEvent
    | SlotEvent;
