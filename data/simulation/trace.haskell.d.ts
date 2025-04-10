/** Haskell simulation trace format */
export interface HaskellTraceEvent {
    time_s: number;
    message: HaskellEvent;
}

type BlockKind = "IB" | "EB" | "RB" | "VTBundle";
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
    slot: number;
}

// Additional fields for Generated events
interface GeneratedBlockEvent extends BaseBlockEvent {
    size_bytes: number;
    producer: string;
}

interface GeneratedInputBlock extends GeneratedBlockEvent {
    id: string;
    payload_bytes?: number;
    rb_ref?: string;
}
interface BlockRef {
  id : string;
}
interface Endorsement {
  eb : BlockRef;
}

interface GeneratedEndorserBlock extends GeneratedBlockEvent {
    id: string;
    input_blocks: BlockRef[];
}

interface GeneratedRankingBlock extends GeneratedBlockEvent {
    endorsement?: Endorsement;
    endorsements?: Endorsement[];
    vrf? : number;
    id? : string;
    payload_bytes? : number;
    parent?: {
        id: string;
    };
}

interface GeneratedVote extends GeneratedBlockEvent {
    id: string;
    votes: Record<string, number>;
}

// EnteredState events only need the base identification info
interface EnteredStateBlock extends BaseBlockEvent {
    id: string;
  node: string;
}

type HaskellBlockEvent =
    | GeneratedInputBlock
    | GeneratedEndorserBlock
    | GeneratedRankingBlock
    | GeneratedVote
    | EnteredStateBlock;
type NetworkAction = "Sent" | "Received"
interface HaskellNetworkEvent {
    type: `${BlockKind}${NetworkAction}`;
    sender?: string;
    recipient: string;
    msg_size_bytes?: number;
    sending_s?: number;
    id: string;
    ids?: string[];
}

// Type to validate `jq '.' -cs` of a log.
type TraceEvents = HaskellTraceEvent[]