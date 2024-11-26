import {
  IServerMessage,
  ITransactionGenerated,
  ITransactionMessage,
  ITransactionReceived,
  ITransactionSent,
} from "@/components/Graph/types";

export interface ITransactionsData {
  byId: Map<number, ITransactionMessage[]>;
  generated: Map<number, IServerMessage<ITransactionGenerated>>;
  sent: Map<number, IServerMessage<ITransactionSent>[]>;
  received: Map<number, IServerMessage<ITransactionReceived>[]>;
}
