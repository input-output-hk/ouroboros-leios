export interface INode {
  id: string;
  location: number[];
  stake?: number;
}

export interface ILink {
  nodes: string[];
}

export interface IServerNodeMap {
  links: ILink[];
  nodes: INode[];
}

export enum EServerType {
  NODE = "node",
  LINK = "link"
}

export type TServerNode = {
  type: EServerType.NODE;
  data: INode;
}

export type TServerLink = {
  type: EServerType.LINK,
  data: ILink;
}

export type TServerNodeMap = TServerNode | TServerLink;

export interface ITransformedNode {
  id: string;
  fx: number;
  fy: number;
  data: {
    location: number[];
    stake?: number;
  };
};

/** source|target */
export type TLinkMapId = string;

export interface ITransformedNodeMap {
  nodes: Map<string, ITransformedNode>;
  links: Map<string, { source: string; target: string }>;
}

export enum EMessageType {
  TransactionGenerated = "TransactionGenerated",
  TransactionReceived = "TransactionReceived",
  TransactionSent = "TransactionSent",
  InputBlockGenerated = "InputBlockGenerated",
  InputBlockReceived = "InputBlockReceived",
  InputBlockSent = "InputBlockSent",
  PraosBlockGenerated = "PraosBlockGenerated",
  PraosBlockReceived = "PraosBlockReceived",
  PraosBlockSent = "PraosBlockSent",
  EndorserBlockGenerated = "EndorserBlockGenerated",
  EndorserBlockReceived = "EndorserBlockReceived",
  EndorserBlockSent = "EndorserBlockSent",
  VotesGenerated = "VotesGenerated",
  VotesReceived = "VotesReceived",
  VotesSent = "VotesSent",
  Slot = "Slot",
}

export interface ITransactionGenerated {
  type: EMessageType.TransactionGenerated;
  id: string;
  publisher: number;
  bytes: number;
}

export interface ITransactionReceived {
  type: EMessageType.TransactionReceived;
  id: string;
  sender: number;
  recipient: number;
}

export interface ITransactionSent {
  type: EMessageType.TransactionSent;
  id: string;
  sender: number;
  recipient: number;
}

export interface IInputBlockGenerated {
  type: EMessageType.InputBlockGenerated;
  id: string;
  slot: number;
  producer: number;
  index: number;
  vrf: number;
  timestamp: number;
  header_bytes: number
  transactions: number[];
}

export interface IInputBlockReceived {
  type: EMessageType.InputBlockReceived;
  id: string;
  slot: number;
  producer: number;
  index: number;
  sender: number;
  recipient: number;
}

export interface IInputBlockSent {
  type: EMessageType.InputBlockSent;
  id: string;
  slot: number;
  producer: number;
  index: number;
  sender: number;
  recipient: number;
}

export interface ISlot {
  type: EMessageType.Slot;
  number: number;
}

export interface IPraosBlockGenerated {
  type: EMessageType.PraosBlockGenerated;
  id: string;
  slot: number;
  producer: number;
  header_bytes: number;
  endorsement: IEndorsement | null;
  transactions: number[];
}

export interface IEndorsement {
  eb: { id: string }
  bytes: number;
  votes: {}
}

export interface IPraosBlockReceived {
  type: EMessageType.PraosBlockReceived;
  id: string;
  slot: number;
  sender: number;
  recipient: number;
}

export interface IPraosBlockSent {
  type: EMessageType.PraosBlockSent;
  slot: number;
  id: string;
  sender: number;
  recipient: number;
}

export interface IEndorserBlockGenerated {
  type: EMessageType.EndorserBlockGenerated;
  id: string;
  slot: number;
  producer: number;
  bytes: number;
  input_blocks: IInputBlock[]
}

export interface IInputBlock {
  id: string;
}

export interface IEndorserBlockReceived {
  type: EMessageType.EndorserBlockReceived;
  id: string;
  slot: number;
  sender: number;
  recipient: number;
}

export interface IEndorserBlockSent {
  type: EMessageType.EndorserBlockSent;
  slot: number;
  id: string;
  sender: number;
  recipient: number;
}

export interface IVotesGenerated {
  type: EMessageType.VotesGenerated;
  id: string;
  slot: number;
  producer: string;
  bytes: number;
  votes: any[] // @todo
}

export interface IVotesReceived {
  type: EMessageType.VotesReceived;
  id: string;
  slot: number;
  sender: number;
  recipient: number;
}

export interface IVotesSent {
  type: EMessageType.VotesSent;
  slot: number;
  id: string;
  sender: number;
  recipient: number;
}

export type TMessageType =
  | IInputBlockGenerated
  | IInputBlockReceived
  | IInputBlockSent
  | IPraosBlockGenerated
  | IPraosBlockReceived
  | IPraosBlockSent
  | IEndorserBlockGenerated
  | IEndorserBlockReceived
  | IEndorserBlockSent
  | IVotesGenerated
  | IVotesReceived
  | IVotesSent
  | ISlot
  | ITransactionGenerated
  | ITransactionReceived
  | ITransactionSent;

export interface IServerMessage<T = TMessageType> {
  time: number;
  message: T;
}

export interface ITransactionMessage {
  id: string;
  generated: number;
  duration: number;
  sentTime: number;
  source: number;
  target: number;
}
