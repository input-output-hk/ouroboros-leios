/** Base simulation trace format */
export interface TraceEvent {
    time_s: number;
    message: Event;
}

type LeiosBlockKind = "IB" | "EB" | "VTBundle"
type BlockKind = LeiosBlockKind | "RB";
type BlockAction = "Generated";

type Event =
    | CpuEvent
    | BlockEvent
    | NetworkEvent
    | SlotEvent
    | NoBlockEvent;

type EventType =
    | CpuEventType
    | BlockEventType
    | NetworkEventType
    | SlotEventType
    | NoBlockEventType;

type SlotEventType = "Slot"
interface SlotEvent {
    type: SlotEventType;
    node: string;
    slot: number;
}

type NoBlockEventType = `No${LeiosBlockKind}Generated`
interface NoBlockEvent {
    type: NoBlockEventType;
    node: string;
    slot: number;
}

type CpuTaskType = "ValIB" | "ValEB" | "ValRB" | "ValIH" | "ValRH" | "ValVote" | "GenIB" | "GenEB" | "GenVote" | "GenRB"
type CpuEventType = "Cpu"
interface CpuEvent {
    type: CpuEventType;
    node: string;
    cpu_time_s: number;
    task_type: CpuTaskType;
    id: string;
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
    pipeline: number;
    tx_payload_bytes: number;
    rb_ref?: string | null;
}
interface BlockRef {
    id: string;
}
interface Endorsement {
    eb: BlockRef;
}

interface GeneratedEndorserBlock extends GeneratedBlockEvent {
    id: string;
    pipeline: number;
    input_blocks: BlockRef[];
}

interface GeneratedVote extends GeneratedBlockEvent {
    id: string;
    pipeline: number;
    votes: { [eb: string]: number };
}

interface GeneratedRankingBlock extends GeneratedBlockEvent {
    endorsement: Endorsement | null;
    endorsements?: Endorsement[] | null;
    id: string;
    tx_payload_bytes: number;
    parent: BlockRef | null;
}

type BlockEvent =
    | GeneratedInputBlock
    | GeneratedEndorserBlock
    | GeneratedRankingBlock
    | GeneratedVote


type NetworkAction = "Sent" | "Received"
type NetworkEventType = `${BlockKind}${NetworkAction}`

interface NetworkEvent {
    type: NetworkEventType;
    sender?: string;
    recipient: string;
    msg_size_bytes?: number;
    sending_s?: number;
    id: string;
    ids?: string[];
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
type TraceEvents = (TraceEvent | UnknownEvent)[]

type KnownType = EventType