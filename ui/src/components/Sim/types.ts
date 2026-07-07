// UI-only topology and rendering types -----------------------------------

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
  links: Map<
    string,
    {
      source: string;
      target: string;
      latencyMs?: number;
      bandwidthBytesPerSecond?: number;
    }
  >;
}

// Message types — thin wrapper over @/schema/trace.ui ---------------------

import type {
  Vote,
  UIRBGenerated,
  UIRBSent,
  UIRBReceived,
  UIEBGenerated,
  UIEBSent,
  UIEBReceived,
  UIVotesGenerated,
  UIVotesSent,
  UIVotesReceived,
  UITxsGenerated,
  UITxsSent,
  UITxsReceived,
  UIMessage,
  UITraceEvent,
} from "@/schema/trace.ui";

/** Type literals branched on at runtime — mirrors `UIMessageType`. */
export enum EServerMessageType {
  TxsGenerated = "TxsGenerated",
  TxsReceived = "TxsReceived",
  TxsSent = "TxsSent",
  EBGenerated = "EBGenerated",
  EBReceived = "EBReceived",
  EBSent = "EBSent",
  VotesGenerated = "VotesGenerated",
  VotesReceived = "VotesReceived",
  VotesSent = "VotesSent",
  RBGenerated = "RBGenerated",
  RBReceived = "RBReceived",
  RBSent = "RBSent",
}

export type IVote = Vote;
export type ITxsGenerated = UITxsGenerated;
export type ITxsReceived = UITxsReceived;
export type ITxsSent = UITxsSent;
export type IRankingBlockGenerated = UIRBGenerated;
export type IRankingBlockReceived = UIRBReceived;
export type IRankingBlockSent = UIRBSent;
export type IEndorserBlockGenerated = UIEBGenerated;
export type IEndorserBlockReceived = UIEBReceived;
export type IEndorserBlockSent = UIEBSent;
export type IVotesGenerated = UIVotesGenerated;
export type IVotesReceived = UIVotesReceived;
export type IVotesSent = UIVotesSent;

export type TServerMessageType = UIMessage;

export type IServerMessage<T = TServerMessageType> = Omit<UITraceEvent, "message"> & {
  message: T;
};
