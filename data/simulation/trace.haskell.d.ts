/** Haskell simulation trace format */
export interface HaskellTraceEvent {
    time_s: number;
    event: HaskellEvent;
}

type MessageKind = "IB" | "EB" | "RB" | "VT";

type HaskellEvent =
    | HaskellCpuEvent
    | HaskellGeneratedEvent
    | HaskellSentEvent
    | HaskellReceivedEvent
    | HaskellStateEvent;

interface HaskellCpuEvent {
    tag: "Cpu";
    node: string;
    node_name: string;
    duration_s: number;
    cpu_time_s: number;
    // CPU task types: Block validation (ValIB, ValEB, ValRB), Header validation (ValIH, ValRH), Vote validation (ValVote). Format: "<task_type>: <id>"
    task_label: string; // e.g., "ValIB: 6-29" or "ValRH: 6253064077348247640"
}

type HaskellGeneratedEvent =
    | HaskellGeneratedIBEvent
    | HaskellGeneratedEBEvent
    | HaskellGeneratedRBEvent
    | HaskellGeneratedVTEvent;

interface HaskellGeneratedBaseEvent {
    tag: "generated";
    node: number;
    node_name: string;
    size_bytes: number;
}

interface HaskellGeneratedIBEvent extends HaskellGeneratedBaseEvent {
    kind: "IB";
    id: string;
    slot: number;
    payload_bytes: number;
    rb_ref: string;
}

interface HaskellGeneratedEBEvent extends HaskellGeneratedBaseEvent {
    kind: "EB";
    id: string;
    input_blocks: string[];
}

interface HaskellGeneratedRBEvent extends HaskellGeneratedBaseEvent {
    kind: "RB";
    id: string;
}

interface HaskellGeneratedVTEvent extends HaskellGeneratedBaseEvent {
    kind: "VT";
    id: string;
    votes: number;
    endorse_blocks: string[];
}

interface HaskellSentEvent {
    tag: "Sent";
    sender: number;
    receipient: number;
    msg_size_bytes: number;
    sending_s: number;
    kind: MessageKind;
    ids: string[];
}

interface HaskellReceivedEvent {
    tag: "received";
    kind: MessageKind;
    id: string;
    node: number;
    node_name: string;
}

interface HaskellStateEvent {
    tag: "enteredstate";
    kind: MessageKind;
    id: string;
    node: number;
    node_name: string;
}
