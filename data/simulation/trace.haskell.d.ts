/** Haskell simulation trace format */
export interface HaskellTraceEvent {
    time_s: number;
    event: HaskellEvent;
}

type HaskellEvent =
    | HaskellCpuEvent
    | HaskellGeneratedEvent
    | HaskellSentEvent
    | HaskellReceivedEvent
    | HaskellStateEvent;

interface HaskellCpuEvent {
    tag: "Cpu";
    node: number;
    node_name: string;
    duration_s: number;
    // CPU task types: Block validation (ValIB, ValEB, ValRB), Header validation (ValIH, ValRH), Vote validation (ValVote). Format: "<task_type>: <id>"
    task_label: string; // e.g., "ValIB: 6-29" or "ValRH: 6253064077348247640"
}

interface HaskellGeneratedEvent {
    tag: "generated";
    kind: "IB" | "EB" | "RB" | "VT";
    id: string;
    node: number;
    node_name: string;
    size_bytes: number;
    // Required for IB
    slot?: number;
    payload_bytes?: number;
    rb_ref?: string;
    // Required for EB
    input_blocks?: string[];
    // Required for VT
    votes?: number;
    endorse_blocks?: string[];
}

interface HaskellSentEvent {
    tag: "Sent";
    sender: number;
    receipient: number;
    msg_size_bytes: number;
    sending_s: number;
    kind: "IB" | "EB" | "RB" | "VT";
    ids: string[];
}

interface HaskellReceivedEvent {
    tag: "received";
    kind: "IB" | "EB" | "RB" | "VT";
    id: string;
    node: number;
    node_name: string;
}

interface HaskellStateEvent {
    tag: "enteredstate";
    kind: "IB" | "EB" | "RB" | "VT";
    id: string;
    node: number;
    node_name: string;
}
