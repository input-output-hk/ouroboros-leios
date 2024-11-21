import { EMessageType, IServerMessage } from "@/components/Graph/types";
import { closeSync, openSync, readSync, statSync } from "fs";
import { NextResponse } from "next/server";
import { messagesPath } from "../../utils";

async function getLastTransactionReceived(filePath: string, bufferSize = 1024): Promise<string> {
  return new Promise((resolve, reject) => {
    const fileSize = statSync(filePath).size;
    if (fileSize === 0) {
      return reject(new Error("File is empty"));
    }

    const fileDescriptor = openSync(filePath, 'r');
    let buffer = Buffer.alloc(bufferSize);
    let position = fileSize;
    let lastLine = "";
    let foundLastTransactionReceived = false;

    while (position > 0 && !foundLastTransactionReceived) {
      // Calculate how many bytes to read
      const bytesToRead = Math.min(bufferSize, position);
      position -= bytesToRead;

      // Read from the file
      readSync(fileDescriptor, new Uint8Array(buffer.buffer), 0, bytesToRead, position);
      const chunk = buffer.toString('utf8', 0, bytesToRead);

      // Search for the last newline character
      const lines = chunk.split(/\n/).reverse();
      for (const line of lines) {
        if (!line) {
          continue;
        }

        try {
          const message: IServerMessage = JSON.parse(line);
          if (message.message.type === EMessageType.TransactionReceived) {
            lastLine = line;
            foundLastTransactionReceived = true;
            break;
          }
        } catch (e) {
          console.log(`Could not parse: ${line}`)
        }
      }

      position -= bytesToRead;
    }

    closeSync(fileDescriptor);

    if (!foundLastTransactionReceived && lastLine.length === 0) {
      return reject(new Error("Could not find any complete line in the file"));
    }

    if (!lastLine) {
      reject("Could not find the last transaction.")
    } else {
      resolve(lastLine.trim());
    }
  });
}

export async function GET() {
  try {
    const line = await getLastTransactionReceived(messagesPath);
    console.log(line)
    const data: IServerMessage = JSON.parse(line);
    return NextResponse.json(data);
  } catch(e) {
    return new NextResponse(null, {
      status: 500
    })
  }
}
