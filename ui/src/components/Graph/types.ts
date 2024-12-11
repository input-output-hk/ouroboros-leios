export interface INode {
  location: number[];
  stake?: number;
}

export interface ILink {
  nodes: number[];
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
  id: number;
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
  nodes: Map<number, ITransformedNode>;
  links: Map<string, { source: number; target: number }>;
}

export enum EMessageType {
  TransactionGenerated = "TransactionGenerated",
  TransactionReceived = "TransactionReceived",
  TransactionSent = "TransactionSent",
  InputBlockReceived = "InputBlockReceived",
  PraosBlockReceived = "PraosBlockReceived",
  Slot = "Slot",
  InputBlockGenerated = "InputBlockGenerated",
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

export interface IInputBlockReceived {
  type: EMessageType.InputBlockReceived;
  slot: number;
  producer: number;
  index: number;
  sender: number;
  recipient: number;
}

export interface IPraosBlockReceived {
  type: EMessageType.PraosBlockReceived;
  slot: number;
  sender: number;
  recipient: number;
}

export interface ISlot {
  type: EMessageType.Slot;
  number: number;
}

export interface IInputBlockGenerated {
  type: EMessageType.InputBlockGenerated;
  slot: number;
  producer: number;
  index: number;
  vrf: number;
  timestamp: number;
  transactions: number[];
}

export type TMessageType =
  | IInputBlockGenerated
  | IInputBlockReceived
  | IPraosBlockReceived
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
