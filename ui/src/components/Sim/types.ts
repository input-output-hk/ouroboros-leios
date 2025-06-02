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
  TransactionGenerated = "TXGenerated",
  TransactionReceived = "TXReceived",
  TransactionSent = "TXSent",
  IBGenerated = "IBGenerated",
  IBReceived = "IBReceived",
  IBSent = "IBSent",
  RBGenerated = "RBGenerated",
  RBReceived = "RBReceived",
  RBSent = "RBSent",
  EBGenerated = "EBGenerated",
  EBReceived = "EBReceived",
  EBSent = "EBSent",
  VTBundleGenerated = "VTBundleGenerated",
  VTBundleReceived = "VTBundleReceived",
  VTBundleSent = "VTBundleSent",
}

export interface ITransactionGenerated {
  type: EMessageType.TransactionGenerated;
  id: string;
  publisher: string;
  size_bytes: number;
}

export interface ITransactionReceived {
  type: EMessageType.TransactionReceived;
  id: string;
  sender: string;
  recipient: string;
}

export interface ITransactionSent {
  type: EMessageType.TransactionSent;
  id: string;
  sender: string;
  recipient: string;
}

export interface IInputBlockGenerated {
  type: EMessageType.IBGenerated;
  id: string;
  slot: number;
  pipeline: number;
  producer: string;
  index: number;
  vrf: number;
  timestamp: number;
  header_bytes: number;
  size_bytes: number;
  transactions: number[];
}

export interface IInputBlockReceived {
  type: EMessageType.IBReceived;
  id: string;
  slot: number;
  producer: string;
  index: number;
  sender: string;
  recipient: string;
}

export interface IInputBlockSent {
  type: EMessageType.IBSent;
  id: string;
  slot: number;
  producer: string;
  index: number;
  sender: string;
  recipient: string;
}

export interface IPraosBlockGenerated {
  type: EMessageType.RBGenerated;
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
  votes: {}
}

export interface IPraosBlockReceived {
  type: EMessageType.RBReceived;
  id: string;
  slot: number;
  sender: string;
  recipient: string;
}

export interface IPraosBlockSent {
  type: EMessageType.RBSent;
  slot: number;
  id: string;
  sender: string;
  recipient: string;
}

export interface IEndorserBlockGenerated {
  type: EMessageType.EBGenerated;
  id: string;
  slot: number;
  pipeline: number;
  producer: string;
  size_bytes: number;
  transactions: ITransaction[];
  input_blocks: IInputBlock[];
  endorser_blocks: IEndorserBlock[];
}

export interface ITransaction {
  id: string;
}

export interface IInputBlock {
  id: string;
}

export interface IEndorserBlock {
  id: string;
}

export interface IEndorserBlockReceived {
  type: EMessageType.EBReceived;
  id: string;
  slot: number;
  sender: string;
  recipient: string;
}

export interface IEndorserBlockSent {
  type: EMessageType.EBSent;
  slot: number;
  id: string;
  sender: string;
  recipient: string;
}

export interface IVotesGenerated {
  type: EMessageType.VTBundleGenerated;
  id: string;
  slot: number;
  producer: string;
  size_bytes: number;
  votes: any[] // @todo
}

export interface IVotesReceived {
  type: EMessageType.VTBundleReceived;
  id: string;
  slot: number;
  sender: string;
  recipient: string;
}

export interface IVotesSent {
  type: EMessageType.VTBundleSent;
  slot: number;
  id: string;
  sender: string;
  recipient: string;
}

export interface IUnknown {
  type: '__unknown';
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
  | ITransactionGenerated
  | ITransactionReceived
  | ITransactionSent
  | IUnknown;

export interface IServerMessage<T = TMessageType> {
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
