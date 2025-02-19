/** Haskell simulation trace format */
export interface HaskellTraceEvent {
    time_s: number;
    event: HaskellEvent;
}

type BlockKind = "IB" | "EB" | "RB" | "VT";
type BlockAction = "Generated" | "EnteredState";

type HaskellEvent =
    | HaskellCpuEvent
    | HaskellBlockEvent // Unified block event type
    | HaskellNetworkEvent; // Combine Sent/Received into network events

interface HaskellCpuEvent {
    type: "Cpu";
    node: string;
    cpu_time_s: number;
    // CPU task types: Block validation (ValIB, ValEB, ValRB), Header validation (ValIH, ValRH), Vote validation (ValVote). Format: "<task_type>: <id>"
    task_label: string; // e.g., "ValIB: 6-29" or "ValRH: 6253064077348247640"
}

// Base block event interface
interface BaseBlockEvent {
    type: `${BlockKind}${BlockAction}`;
    node: string;
    id: string;
    size_bytes: number;
    slot: number;
}

interface InputBlockEvent extends BaseBlockEvent {
    payload_bytes: number;
    rb_ref: string; // Reference to ranking block
}

interface EndorserBlockEvent extends BaseBlockEvent {
    input_blocks: string[]; // References to input blocks
}

interface RankingBlockEvent extends BaseBlockEvent {
    endorse_blocks: string[]; // References to certified endorser blocks
    payload_bytes: number; // Size of directly included transactions
}

interface VoteEvent extends BaseBlockEvent {
    votes: number;
    endorse_blocks: string[]; // References to endorser blocks
}

type HaskellBlockEvent =
    | InputBlockEvent
    | EndorserBlockEvent
    | RankingBlockEvent
    | VoteEvent;

interface HaskellNetworkEvent {
    type: "NetworkMessage";
    action: "Sent" | "Received"; // Added to distinguish direction
    sender: string;
    recipient: string;
    block_kind: BlockKind;
    msg_size_bytes: number;
    sending_s: number;
    ids: string[];
}
