import { headers } from "next/headers";
import { IServerMessage, IServerNodeMap, ITransformedNodeMap } from "./types";

export const getFullUrl = async (endpoint: string) => {
  const headersList = await headers()
  const domain = headersList.get('host')
  const protocol = headersList.get('x-forwarded-proto') || 'http'
  const fullUrl = `${protocol}://${domain}`
  return new URL(endpoint, fullUrl).toString();
}

export const getMessages = async (): Promise<IServerMessage[]> => {
  const url = await getFullUrl("/api/messages");
  return fetch(url, {
    cache: "force-cache"
  }).then(async ({ body }) => {
    if (!body) {
      throw new Error("No body found.")
    }

    const messages: IServerMessage[] = [];
    const reader = body.getReader();
    const decoder = new TextDecoder();
    while (true) {
      const { done, value } = await reader.read();
      if (done) {
        break;
      }

      const jsonl = decoder.decode(value);
      jsonl.split(/\n/).forEach((line) => {
        if (!line) {
          return;
        }

        const message = JSON.parse(line);
        messages.push(message);
      });
    }

    return messages;
  });
}

export const getTopography = async (): Promise<ITransformedNodeMap> => {
  const url = await getFullUrl("/api/topography");
  return fetch(url, {
    cache: "force-cache"
  }).then(async ({ body }) => {
    if (!body) {
      throw new Error("No body found.")
    }

    const newMap: ITransformedNodeMap = {
      links: [],
      nodes: []
    };
    const reader = body.getReader();
    const decoder = new TextDecoder();
    while (true) {
      const { done, value } = await reader.read();
      if (done) {
        break;
      }

      const json: IServerNodeMap = JSON.parse(decoder.decode(value));
      newMap.links = newMap.links.concat(
        json.links.map((l) => ({
          source: l.nodes[0],
          target: l.nodes[1],
        })),
      );
      newMap.nodes = newMap.nodes.concat(
        json.nodes.map((n, i) => ({
          id: i,
          fx: n.location[0],
          fy: n.location[1],
          data: n,
        })),
      );
    }

    return newMap;
  });
}
