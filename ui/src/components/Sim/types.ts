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
  LINK = "link",
}

export type TServerNode = {
  type: EServerType.NODE;
  data: INode;
};

export type TServerLink = {
  type: EServerType.LINK;
  data: ILink;
};

export type TServerNodeMap = TServerNode | TServerLink;

export interface ITransformedNode {
  id: string;
  fx: number;
  fy: number;
  data: {
    location: number[];
    stake?: number;
  };
}

/** source|target */
export type TLinkMapId = string;

export interface ITransformedNodeMap {
  nodes: Map<string, ITransformedNode>;
  links: Map<string, { source: string; target: string; latencyMs?: number }>;
}

export enum EServerMessageType {
  TransactionGenerated = "TXGenerated",
  TransactionReceived = "TXReceived",
  TransactionSent = "TXSent",
  EBGenerated = "EBGenerated",
  EBReceived = "EBReceived",
  EBSent = "EBSent",
  VTBundleGenerated = "VTBundleGenerated",
  VTBundleReceived = "VTBundleReceived",
  VTBundleSent = "VTBundleSent",
  RBGenerated = "RBGenerated",
  RBReceived = "RBReceived",
  RBSent = "RBSent",
}

export interface ITransactionGenerated {
  type: EServerMessageType.TransactionGenerated;
  id: string;
  publisher: string;
  size_bytes: number;
}

export interface ITransactionReceived {
  type: EServerMessageType.TransactionReceived;
  id: string;
  sender: string;
  recipient: string;
}

export interface ITransactionSent {
  type: EServerMessageType.TransactionSent;
  id: string;
  sender: string;
  recipient: string;
}


export interface IRankingBlockGenerated {
  type: EServerMessageType.RBGenerated;
  id: string;
  slot: number;
  producer: string;
  header_bytes: number;
  size_bytes: number;
  endorsement: IEndorsement | null;
  transactions: number[];
}

export interface IEndorsement {
  eb: { id: string };
  size_bytes: number;
  votes: {};
}

export interface IRankingBlockReceived {
  type: EServerMessageType.RBReceived;
  id: string;
  slot: number;
  sender: string;
  recipient: string;
}

export interface IRankingBlockSent {
  type: EServerMessageType.RBSent;
  slot: number;
  id: string;
  sender: string;
  recipient: string;
}

export interface IEndorserBlockGenerated {
  type: EServerMessageType.EBGenerated;
  id: string;
  slot: number;
  pipeline: number;
  producer: string;
  size_bytes: number;
  transactions: ITransaction[];
  endorser_blocks: IEndorserBlock[];
}

export interface ITransaction {
  id: string;
}


export interface IEndorserBlock {
  id: string;
}

export interface IEndorserBlockReceived {
  type: EServerMessageType.EBReceived;
  id: string;
  slot: number;
  sender: string;
  recipient: string;
}

export interface IEndorserBlockSent {
  type: EServerMessageType.EBSent;
  slot: number;
  id: string;
  sender: string;
  recipient: string;
}

export interface IVotesGenerated {
  type: EServerMessageType.VTBundleGenerated;
  id: string;
  slot: number;
  producer: string;
  size_bytes: number;
  votes: any[]; // @todo
}

export interface IVotesReceived {
  type: EServerMessageType.VTBundleReceived;
  id: string;
  slot: number;
  sender: string;
  recipient: string;
}

export interface IVotesSent {
  type: EServerMessageType.VTBundleSent;
  slot: number;
  id: string;
  sender: string;
  recipient: string;
}

export interface IUnknown {
  type: "__unknown";
}

export type TServerMessageType =
  | IRankingBlockGenerated
  | IRankingBlockReceived
  | IRankingBlockSent
  | IEndorserBlockGenerated
  | IEndorserBlockReceived
  | IEndorserBlockSent
  | IVotesGenerated
  | IVotesReceived
  | IVotesSent
  | ITransactionGenerated
  | ITransactionReceived
  | ITransactionSent
  | IUnknown;

// TODO: should rename ServerMessage -> ServerMessage
export interface IServerMessage<T = TServerMessageType> {
  time_s: number;
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
