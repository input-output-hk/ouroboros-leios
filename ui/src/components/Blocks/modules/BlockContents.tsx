import { ISimulationBlock, ISimulationTransaction } from '@/contexts/SimContext/types';
import { FC, MouseEvent, PropsWithChildren, useMemo, useState } from "react";

export interface IBlockContentsProps {
  block: ISimulationBlock;
}

interface IBoxProps extends PropsWithChildren {
  selected?: boolean;
  onClick?: (e: MouseEvent) => void;
}

const Box: FC<IBoxProps> = ({ selected, onClick, children }) => {
  const color = selected ? "border-black" : "border-gray-400";
  const cursor = onClick ? "cursor-pointer" : "";
  return (
    <span onClick={onClick} className={`border-2 border-solid ${color} w-48 h-16 flex flex-col items-center justify-center text-center ${cursor}`}>
      {children}
    </span>
  )
}

interface ITXStats {
  name: string;
  txs: ISimulationTransaction[];
}

const Stats: FC<ITXStats> = ({ name, txs }) => {
  const count = txs.length;
  const size = txs.reduce((sum, tx) => sum + tx.bytes, 0);
  return (
    <div className="flex flex-col items-center justify-between gap-4 z-10 absolute right-10 top-10">
      <div className={`flex flex-col gap-4 backdrop-blur-sm bg-white/80 text-xl min-w-[300px]`}>
        <div className="border-2 border-gray-200 rounded p-4">
          <h2 className='font-bold uppercase mb-2'>{name} Transactions</h2>
          <h4 className="flex items-center justify-between gap-4">Transaction Count: <span>{count}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Total size (bytes): <span>{size}</span></h4>
        </div>
      </div>
    </div>
  )
}

export const BlockContents: FC<IBlockContentsProps> = ({ block }) => {
  const stats = useMemo(() => {
    const result: Map<string, ITXStats> = new Map();
    result.set("block", { name: "L1 Block", txs: block.txs });
    if (block.endorsement) {
      for (const ib of block.endorsement.ibs) {
        result.set(ib.id, { name: "Input Block", txs: ib.txs });
      }
    }
    return result;
  }, [block]);

  const [selected, setSelected] = useState<string | null>(null);
  const selectBox = (box: string | null) => (e: MouseEvent) => {
    e.stopPropagation();
    setSelected(box);
  };

  const eb = block.endorsement;
  const ibs = block.endorsement?.ibs ?? [];

  return (
    <>
      {selected && <Stats {...stats.get(selected)!} />}

      <div className='flex flex-col w-full h-3/5 items-center' onClick={selectBox(null)}>
        <h2 className='font-bold text-xl'>Block Transactions</h2>
        <div className="flex w-full h-full gap-8 items-center justify-center">
          <Box selected={selected === "block"} onClick={selectBox("block")}>
            Block
            <span className='text-sm'>Slot {block.slot}</span>
          </Box>
          {eb && <Box>
            Endorsement Block
            <span className='text-sm'>{eb.id}</span>
          </Box>}
          {ibs.length ? (
            <div className="flex flex-col gap-2">
              {ibs.map(ib => (
                <Box key={ib.id} selected={selected === ib.id} onClick={selectBox(ib.id)}>
                  Input Block
                  <span className="text-sm">{ib.id}</span>
                </Box>
              ))}
            </div>
          ) : null}
        </div>

      </div>
    </>
  );
}