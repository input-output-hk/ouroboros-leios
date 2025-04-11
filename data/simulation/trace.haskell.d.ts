/** Haskell simulation trace format */
export interface HaskellTraceEvent {
    time_s: number;
    message: HaskellEvent;
}

type BlockKind = "IB" | "EB" | "RB" | "VTBundle";
type BlockAction = "Generated" | "EnteredState";

type HaskellEvent =
    | HaskellCpuEvent
    | HaskellBlockEvent
    | HaskellNetworkEvent;

type HaskellEventType =
    | CpuEventType
    | BlockEventType
    | NetworkEventType;


type CpuEventType = "Cpu"
interface HaskellCpuEvent {
    type: CpuEventType;
    node: string;
    cpu_time_s: number;
    // CPU task types: Block validation (ValIB, ValEB, ValRB), Header validation (ValIH, ValRH), Vote validation (ValVote). Format: "<task_type>: <id>"
    task_label: string; // e.g., "ValIB: 6-29" or "ValRH: 6253064077348247640"
}

type BlockEventType = `${BlockKind}${BlockAction}`
// Base block event interface with just identification info
interface BaseBlockEvent {
    type: BlockEventType;
    slot: number;
}

// Additional fields for Generated events
interface GeneratedBlockEvent extends BaseBlockEvent {
    size_bytes: number;
    producer: string;
}

interface GeneratedInputBlock extends GeneratedBlockEvent {
    id: string;
    payload_bytes?: number|null;
    rb_ref?: string|null;
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
    endorsement?: Endorsement|null;
    endorsements?: Endorsement[]|null;
    vrf? : number;
    id? : string;
    payload_bytes? : number|null;
    parent?: {
        id: string;
    }|null;
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
type NetworkEventType = `${BlockKind}${NetworkAction}`

interface HaskellNetworkEvent {
    type: NetworkEventType;
    sender?: string|null;
    recipient: string;
    msg_size_bytes?: number|null;
    sending_s?: number|null;
    id: string;
    ids?: string[]|null;
}

export interface UnknownEvent {
    time_s: number;
    message: UnknownMessage;
}

export interface UnknownMessage {
  /** @$ref "#/definitions/UnknownType" */
  type;
}

// Type to validate `jq '.' -cs` of a log.
type TraceEvents = (HaskellTraceEvent|UnknownEvent)[]

type KnownType = HaskellEventType