import {
  EMessageType,
  IServerMessage,
  ITransactionGenerated,
  ITransactionMessage,
  ITransactionReceived,
  ITransactionSent,
} from "@/components/Graph/types";
import { createReadStream, statSync } from "fs";
import readline from "readline";
import { ITransactionsData } from "./types";

export const processMessage = (json: IServerMessage, {
  byId,
  generated,
  sent,
  received
}: ITransactionsData) => {
  const { message } = json;

  if (message.type === EMessageType.TransactionGenerated) {
    generated.set(
      message.id,
      json as IServerMessage<ITransactionGenerated>,
    );
  } else if (message.type === EMessageType.TransactionSent) {
    let sentMessages = sent.get(message.id) || [];
    sentMessages.push(json as IServerMessage<ITransactionSent>);
    sent.set(message.id, sentMessages);

    // Generation will always come first.
    const generatedMsg = generated.get(
      message.id,
    ) as IServerMessage<ITransactionGenerated>;
    const receivedMessages = received.get(message.id) || [];

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

        let transactionList = byId.get(message.id) || [];
        transactionList.push(transaction);
        byId.set(message.id, transactionList);
      }
    }
  } else if (message.type === EMessageType.TransactionReceived) {
    let receivedMessages = received.get(message.id) || [];
    receivedMessages.push(json as IServerMessage<ITransactionReceived>);
    received.set(message.id, receivedMessages);

    const generatedMsg = generated.get(
      message.id,
    ) as IServerMessage<ITransactionGenerated>;
    const sentMessages = sent.get(message.id) || [];

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

        let transactionList = byId.get(message.id) || [];
        transactionList.push(transaction);
        byId.set(message.id, transactionList);
      }
    }
  }
};

export async function findStartPosition(filePath: string, targetTimestamp: number) {
  const fileSize = statSync(filePath).size;
  let left = 0;
  let right = fileSize;
  let bestPosition = 0;

  while (left <= right) {
    const middle = Math.floor((left + right) / 2);
    const timestampAtMiddle = await getTimestampAtPosition(filePath, middle);

    if (timestampAtMiddle < targetTimestamp) {
      left = middle + 1;
    } else {
      bestPosition = middle;
      right = middle - 1;
    }
  }

  return bestPosition;
}

export function getTimestampAtPosition(
  filePath: string,
  position: number,
): Promise<number> {
  return new Promise((resolve, reject) => {
    const stream = createReadStream(filePath, { start: position });
    let foundNewLine = false;
    let adjustedPosition = position;

    // Read a few bytes to find the newline character
    stream.on("data", (chunk) => {
      const decoded = chunk.toString("utf8");
      for (let i = 0; i < decoded.length; i++) {
        if (decoded[i] === "\n") {
          foundNewLine = true;
          adjustedPosition += i + 1; // Move to the start of the next line
          break;
        }
      }

      stream.close(); // Stop reading once the newline is found
    });

    stream.on("close", () => {
      if (foundNewLine) {
        // Now use readline to get the timestamp from the new line
        const lineStream = createReadStream(filePath, {
          start: adjustedPosition,
        });
        const rl = readline.createInterface({
          input: lineStream,
          crlfDelay: Infinity,
        });

        rl.on("line", (line) => {
          const message: IServerMessage = JSON.parse(line);
          const timestamp = message.time / 1_000_000;
          rl.close();
          resolve(timestamp);
        });

        rl.on("error", (err) => {
          reject(err);
        });
      } else {
        reject(
          new Error("Could not find a newline character in the provided range"),
        );
      }
    });

    stream.on("error", (err) => {
      reject(err);
    });
  });
}
