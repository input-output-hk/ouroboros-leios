import { useCallback, useRef } from "react";

import { useGraphContext } from "@/contexts/GraphContext/context";
import {
  EMessageType,
  IServerMessage,
  ITransactionGenerated,
  ITransactionMessage,
  ITransactionReceived,
  ITransactionSent
} from "../types";

export const useStreamMessagesHandler = () => {
  const { dispatch } = useGraphContext();
  const eventSource = useRef<EventSource>();

  // Mutable refs to store messages and transactions without causing re-renders
  const transactionsByIdRef = useRef<Map<number, ITransactionMessage[]>>(new Map());
  const txGeneratedMessagesById = useRef<Map<number, IServerMessage<ITransactionGenerated>>>(new Map());
  const txSentMessagesById = useRef<Map<number, IServerMessage<ITransactionSent>[]>>(new Map());
  const txReceivedMessagesById = useRef<Map<number, IServerMessage<ITransactionReceived>[]>>(new Map());

  const startStream = useCallback(
    (startTime: number, range: number) => {
      const url = new URL('/api/messages/batch', window.location.href);
      url.searchParams.set('startTime', startTime.toString());
      url.searchParams.set('speed', range.toString());

      eventSource.current = new EventSource(url);
      eventSource.current.onmessage = function (message) {
        const json: IServerMessage = JSON.parse(message.data);
        processMessage(json);
      };
    },
    [],
  );

  const stopStream = useCallback(() => {
    eventSource.current?.close();
  }, [])

  // Function to process each message and update transactions
  const processMessage = useCallback((json: IServerMessage) => {
    const { message } = json;

    if (message.type === EMessageType.TransactionGenerated) {
      txGeneratedMessagesById.current.set(message.id, json as IServerMessage<ITransactionGenerated>);
    } else if (message.type === EMessageType.TransactionSent) {
      let sentMessages = txSentMessagesById.current.get(message.id) || [];
      sentMessages.push(json as IServerMessage<ITransactionSent>);
      txSentMessagesById.current.set(message.id, sentMessages);

      // Generation will always come first.
      const generatedMsg = txGeneratedMessagesById.current.get(message.id) as IServerMessage<ITransactionGenerated>;
      const receivedMessages = txReceivedMessagesById.current.get(message.id) || [];

      for (const receivedMsg of receivedMessages) {
        if (
          receivedMsg.message.sender === message.sender &&
          receivedMsg.message.recipient === message.recipient
        ) {
          const transaction: ITransactionMessage = {
            id: message.id,
            duration:
              Math.floor(receivedMsg.time / 1_000_000) -
              Math.floor(json.time / 1_000_000),
            source: message.sender,
            target: message.recipient,
            sentTime: Math.floor(json.time / 1_000_000),
            generated: Math.floor(generatedMsg?.time || 0 / 1_000_000),
          };

          let transactionList = transactionsByIdRef.current.get(message.id) || [];
          transactionList.push(transaction);
          transactionsByIdRef.current.set(message.id, transactionList);
        }
      }
    } else if (message.type === EMessageType.TransactionReceived) {
      let receivedMessages = txReceivedMessagesById.current.get(message.id) || [];
      receivedMessages.push(json as IServerMessage<ITransactionReceived>);
      txReceivedMessagesById.current.set(message.id, receivedMessages);

      const generatedMsg = txGeneratedMessagesById.current.get(message.id) as IServerMessage<ITransactionGenerated>;
      const sentMessages = txSentMessagesById.current.get(message.id) || [];

      for (const sentMsg of sentMessages) {
        if (
          sentMsg.message.sender === message.sender &&
          sentMsg.message.recipient === message.recipient
        ) {
          const transaction: ITransactionMessage = {
            id: message.id,
            duration:
              Math.floor(json.time / 1_000_000) -
              Math.floor(sentMsg.time / 1_000_000),
            source: message.sender,
            target: message.recipient,
            sentTime: Math.floor(sentMsg.time / 1_000_000),
            generated: Math.floor(generatedMsg?.time || 0 / 1_000_000),
          };

          let transactionList = transactionsByIdRef.current.get(message.id) || [];
          transactionList.push(transaction);
          transactionsByIdRef.current.set(message.id, transactionList);
        }
      }
    }
  }, []);

  return {
    startStream,
    stopStream,
    transactionsRef: transactionsByIdRef,
    txGeneratedRef: txGeneratedMessagesById,
    txSentMessagesRef: txSentMessagesById,
    txReceivedMessagesRef: txReceivedMessagesById
  };
};
