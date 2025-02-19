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

// Base block event interface with just identification info
interface BaseBlockEvent {
    type: `${BlockKind}${BlockAction}`;
    node: string;
    id: string;
    slot: number;
}

// Additional fields for Generated events
interface GeneratedBlockEvent extends BaseBlockEvent {
    size_bytes: number;
}

interface GeneratedInputBlock extends GeneratedBlockEvent {
    payload_bytes: number;
    rb_ref: string;
}

interface GeneratedEndorserBlock extends GeneratedBlockEvent {
    input_blocks: string[];
}

interface GeneratedRankingBlock extends GeneratedBlockEvent {
    endorse_blocks: string[];
    payload_bytes: number;
}

interface GeneratedVote extends GeneratedBlockEvent {
    votes: number;
    endorse_blocks: string[];
}

// EnteredState events only need the base identification info
type EnteredStateBlock = BaseBlockEvent;

type HaskellBlockEvent =
    | GeneratedInputBlock
    | GeneratedEndorserBlock
    | GeneratedRankingBlock
    | GeneratedVote
    | EnteredStateBlock;

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
