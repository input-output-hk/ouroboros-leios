import { useSimContext } from "@/contexts/SimContext/context";
import { FC } from "react";
import { BlockContents } from "./modules/BlockContents";
import { BlockGraph } from "./modules/BlockGraph";

export const BlocksView: FC = ({}) => {
  const {
    state: {
      blocks: { currentBlock },
      aggregatedData: { blocks },
    },
  } = useSimContext();
  const block = currentBlock !== undefined ? blocks[currentBlock] : null;
  if (block) {
    return <BlockContents block={block} />;
  }
  return <BlockGraph />;
};
