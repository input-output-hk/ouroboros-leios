// import { headers } from "next/headers";
import oboe from "oboe";
import { Dispatch, SetStateAction } from "react";
import { EServerType, IServerMessage, ITransformedNodeMap, TServerNodeMap } from "./types";

// export const getFullUrl = async (endpoint: string) => {
//   const headersList = await headers()
//   const domain = headersList.get('host')
//   const protocol = headersList.get('x-forwarded-proto') || 'http'
//   const fullUrl = `${protocol}://${domain}`
//   return new URL(endpoint, fullUrl).toString();
// }

export const getMessages = async (): Promise<IServerMessage[]> => {
  // const url = await getFullUrl("/api/messages");
  // return fetch(url, {
  //   cache: "force-cache"
  // }).then(async ({ body }) => {
  //   if (!body) {
  //     throw new Error("No body found.")
  //   }

  //   const messages: IServerMessage[] = [];
  //   const reader = body.getReader();
  //   const decoder = new TextDecoder();
  //   while (true) {
  //     const { done, value } = await reader.read();
  //     if (done) {
  //       break;
  //     }

  //     const jsonl = decoder.decode(value);
  //     jsonl.split(/\n/).forEach((line) => {
  //       if (!line) {
  //         return;
  //       }

  //       const message = JSON.parse(line);
  //       messages.push(message);
  //     });
  //   }

  //   return messages;
  // });

  return [];
};

export const streamMessages = (
  setMessages: Dispatch<SetStateAction<Set<IServerMessage>>>,
  range: number
) => {
  const url = new URL("/api/messages", window.location.href);
  url.searchParams.set("time", range.toString());

  oboe(url.toString())
    .node("!", (res: IServerMessage) => {
      setMessages((prev) => {
        const newResult = new Set(prev);
        newResult.add(res);

        return newResult;
      });

      return oboe.drop;
    })
};

export const streamTopography = (
  setNodeMap: Dispatch<SetStateAction<ITransformedNodeMap>>,
) => {
  oboe("/api/topography")
    .node("!", (res: TServerNodeMap) => {
      setNodeMap((prev) => {
        const newResult = {...prev};
        
        if (res.type === EServerType.NODE) {
          newResult.nodes.push({
            data: res.data,
            fx: res.data.location[0],
            fy: res.data.location[1],
            id: prev.nodes.length
          });
        } else {
          newResult.links.push({
            source: res.data.nodes[0],
            target: res.data.nodes[1]
          })
        }

        return newResult;
      });
    })
};
