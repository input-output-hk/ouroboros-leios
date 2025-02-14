/** Rust simulation trace format */

// Base types
interface RustBaseEvent {
    time: number; // nanoseconds
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
type RustCpuTaskType =
    | "PraosBlockValidated"
    | "EndorserBlockValidated"
    | "VoteBundleValidated"
    | "EndorserBlockGenerated"
    | "VoteBundleGenerated"
    | "InputBlockValidated"
    | "InputBlockGenerated"
    | "TransactionValidated"
    | "PraosBlockGenerated";

type RustCpuMessageType =
    | "CpuTaskScheduled"
    | "CpuTaskFinished"
    | "CpuSubtaskStarted"
    | "CpuSubtaskFinished";

interface RustCpuEvent extends Omit<RustBaseEvent, "message"> {
    message: {
        type: RustCpuMessageType;
        task: RustTaskInfo;
        task_type?: RustCpuTaskType;
        subtasks?: number;
        subtask_id?: number;
        extra?: string;
    };
}

// Block Events
interface RustBaseBlockEvent {
    id?: string;
    slot: number;
    producer: string;
    sender?: string;
    recipient?: string;
}

type RustInputBlockMessageType =
    | "InputBlockSent"
    | "InputBlockReceived"
    | "InputBlockLotteryWon"
    | "InputBlockGenerated";

interface RustInputBlockEvent extends Omit<RustBaseEvent, "message"> {
    message: RustBaseBlockEvent & {
        type: RustInputBlockMessageType;
        index: number;
        header_bytes?: number;
        transactions?: string[];
    };
}

type RustEndorserBlockMessageType =
    | "EndorserBlockSent"
    | "EndorserBlockReceived"
    | "EndorserBlockLotteryWon"
    | "EndorserBlockGenerated";

interface RustEndorserBlockEvent extends Omit<RustBaseEvent, "message"> {
    message: RustBaseBlockEvent & {
        type: RustEndorserBlockMessageType;
    };
}

type RustPraosBlockMessageType =
    | "PraosBlockSent"
    | "PraosBlockReceived"
    | "PraosBlockLotteryWon"
    | "PraosBlockGenerated";

interface RustPraosBlockEvent extends Omit<RustBaseEvent, "message"> {
    message: RustBaseBlockEvent & {
        type: RustPraosBlockMessageType;
        header_bytes?: number;
        transactions?: string[];
        vrf?: number;
        endorsement?: any;
    };
}

// Transaction Events
type RustTransactionMessageType =
    | "TransactionSent"
    | "TransactionReceived"
    | "TransactionGenerated";

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
type RustVoteMessageType =
    | "VotesReceived"
    | "VotesSent"
    | "VotesGenerated"
    | "VoteLotteryWon";

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
    | RustInputBlockEvent
    | RustEndorserBlockEvent
    | RustPraosBlockEvent
    | RustTransactionEvent
    | RustVoteEvent
    | RustSlotEvent;
