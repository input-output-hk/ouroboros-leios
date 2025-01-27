import { ISimulationBlock, ISimulationTransaction } from '@/contexts/SimContext/types';
import { FC, MouseEvent, PropsWithChildren, useMemo, useState } from "react";

export interface IBlockContentsProps {
  block: ISimulationBlock;
}

interface IBoxProps extends PropsWithChildren {
  selected?: boolean;
  proportion?: number;
  onClick?: (e: MouseEvent) => void;
}

const Box: FC<IBoxProps> = ({ selected, proportion = 1, onClick, children }) => {
  const color = selected ? "border-black" : "border-gray-400";
  const cursor = onClick ? "cursor-pointer" : "";
  return (
    <span onClick={onClick} className={`border-2 border-solid ${color} w-48 min-h-16 max-h-48 flex flex-col items-center justify-center text-center ${cursor}`} style={{
      height: 32 * proportion
    }}>
      {children}
    </span>
  )
}

interface ITXStats {
  name: string;
  slot: number;
  txs: ISimulationTransaction[];
}

interface IStatsProps {
  name: string;
  slot: number;
  txs: ISimulationTransaction[];
  position: [number, number];
}

const Stats: FC<IStatsProps> = ({ name, slot, txs, position: [left, top] }) => {
  const count = txs.length;
  const size = txs.reduce((sum, tx) => sum + tx.bytes, 0);
  return (
    <div className="flex flex-col items-center justify-between gap-4 z-10 absolute" style={{ left, top }}>
      <div className={`flex flex-col gap-4 backdrop-blur-sm bg-white/80 text-xl min-w-[300px]`}>
        <div className="border-2 border-black rounded p-4">
          <h2 className='font-bold uppercase mb-2'>{name}</h2>
          <h4 className="flex items-center justify-between gap-4">Created in slot: <span>{slot}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Transaction count: <span>{count}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Total size (bytes): <span>{size}</span></h4>
        </div>
      </div>
    </div>
  )
}

interface SelectState {
  key: string,
  position: [number, number]
}

export const BlockContents: FC<IBlockContentsProps> = ({ block }) => {
  const stats = useMemo(() => {
    const result: Map<string, ITXStats> = new Map();
    result.set("block", { name: "L1 Block", slot: block.slot, txs: block.txs });
    if (block.endorsement) {
      for (const ib of block.endorsement.ibs) {
        result.set(ib.id, { name: "Input Block", slot: ib.slot, txs: ib.txs });
      }
    }
    return result;
  }, [block]);

  const [selected, setSelected] = useState<SelectState | null>(null);
  const selectBox = (box: string | null) => (e: MouseEvent) => {
    e.stopPropagation();
    if (box) {
      setSelected({
        key: box,
        position: [e.pageX, e.pageY],
      });
    } else {
      setSelected(null);
    }
  };

  const eb = block.endorsement;
  const ibs = block.endorsement?.ibs ?? [];

  return (
    <>
      {selected && <Stats {...stats.get(selected.key)!} position={selected.position} />}

      <div className='flex flex-col w-full h-3/5 items-center' onClick={selectBox(null)}>
        <h2 className='font-bold text-xl'>Block Transactions</h2>
        <div className="flex w-full h-full gap-8 items-center justify-center">
          {ibs.length ? (
            <div className="flex flex-col gap-2">
              {ibs.map(ib => {
                const isSelected = selected?.key === ib.id;
                const proportion = 2 * ib.txs.length / block.txs.length;
                return (
                  <Box key={ib.id} selected={isSelected} proportion={proportion} onClick={selectBox(ib.id)}>
                    Input Block
                    <span className="text-sm">Slot {ib.slot}, {ib.txs.length} TX</span>
                  </Box>
                );
              })}
            </div>
          ) : null}
          {eb && <Box proportion={1}>
            Endorsement Block
            <span className='text-sm'>Slot {eb.slot}</span>
          </Box>}
          <Box selected={selected?.key === "block"} proportion={2} onClick={selectBox("block")}>
            Block
            <span className='text-sm'>Slot {block.slot}, {block.txs.length} TX</span>
          </Box>
        </div>

      </div>
    </>
  );
}