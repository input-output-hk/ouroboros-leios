export interface INode {
  location: number[];
  stake?: number;
}

export interface IServerNodeMap {
  nodes: INode[];
  links: {
    nodes: number[];
    id?: number;
  }[];
}

export interface ITransformedNode {
  id: number;
  fx: number;
  fy: number;
  data: {
    location: number[];
    stake?: number;
  };
};

export interface ITransformedNodeMap {
  nodes: ITransformedNode[];
  links: {
    source: number;
    target: number;
  }[];
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
  id: number;
  publisher: number;
  bytes: number;
}

export interface ITransactionReceived {
  type: EMessageType.TransactionReceived;
  id: number;
  sender: number;
  recipient: number;
}

export interface ITransactionSent {
  type: EMessageType.TransactionSent;
  id: number;
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
  generated: number;
  duration: number;
  sentTime: number;
  source: number;
  target: number;
}

export interface ITransactionRoundTrip {
  generated: number;
  trip: {
    source: number;
    target: number;
    duration: number;
  }[];
}
