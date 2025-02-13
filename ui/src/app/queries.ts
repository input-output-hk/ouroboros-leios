import {
  ILink,
  INode,
  IServerNodeMap
} from "@/components/Sim/types";
import { readFile } from "fs";
import path from "path";
import { promisify } from "util";
import { parse } from "yaml";
import { Coord2D, Node as IServerNode } from '../../../data/simulation/topology';
import { getMaxTime, messagesPath } from "./api/utils";

const readFileAsync = promisify(readFile);

export const getSimulationMaxTime = async (): Promise<number> => {
  return await getMaxTime(messagesPath);
};

export const getSimulationTopography = async (): Promise<IServerNodeMap> => {
  const filePath = path.resolve(
    __dirname,
    "../../../../../sim-rs/test_data/thousand.yaml",
  );
  const file = await readFileAsync(filePath, { encoding: 'utf8' });
  const yaml = parse(file);

  const nodes: INode[] = [];
  const links = new Map<String, ILink>();
  for (const [id, node] of Object.entries<IServerNode<Coord2D>>(yaml.nodes)) {
    nodes.push({
      id,
      location: node.location,
      stake: node.stake as unknown as number,
    });
    for (const peerId of Object.keys(node.producers)) {
      const linkIds = [id, peerId].sort();
      links.set(JSON.stringify(linkIds), { nodes: linkIds });
    }
  }

  return { nodes, links: [...links.values()] };
}
