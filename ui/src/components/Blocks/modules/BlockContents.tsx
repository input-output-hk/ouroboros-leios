import { ISimulationBlock, ISimulationTransaction } from '@/contexts/SimContext/types';
import cx from "classnames";
import { FC, MouseEvent, PropsWithChildren, useMemo, useState } from "react";

import classes from "./styles.module.css";

export interface IBlockContentsProps {
  block: ISimulationBlock;
}

interface IBoxProps extends PropsWithChildren {
  className?: string;
  selected?: boolean;
  proportion?: number;
  onClick?: (e: MouseEvent) => void;
}

const Box: FC<IBoxProps> = ({ selected, proportion = 1, onClick, children, className }) => {
  const color = selected ? "border-black" : "border-gray-400";
  return (
    <span onClick={onClick} className={cx("border-2 border-solid w-48 min-h-16 max-h-48 flex flex-col items-center justify-center text-center", color, { 'cursor-pointer': !!onClick }, className)} style={{
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
  breakdown: [string, number][];
}

interface IStatsProps {
  name: string;
  slot: number;
  txs: ISimulationTransaction[];
  breakdown: [string, number][];
  position: [number, number];
}

const printBytes = (bytes: number) => {
  if (bytes >= 1024 * 1024) {
    return `${(bytes / 1024 / 1024).toFixed(3)} MB`;
  }
  if (bytes >= 1024) {
    return `${(bytes / 1024).toFixed(3)} KB`;
  }
  return `${bytes} bytes`;
}

const Stats: FC<IStatsProps> = ({ name, slot, txs, breakdown, position: [left, top] }) => {
  const count = txs.length;
  const txBytes = txs.reduce((sum, tx) => sum + tx.bytes, 0);
  const totalBytes = breakdown.reduce((sum, el) => sum + el[1], txBytes);
  return (
    <div className="flex flex-col items-center justify-between gap-4 z-10 absolute" style={{ left, top }}>
      <div className="flex flex-col gap-4 backdrop-blur-sm bg-white/80 text-xl min-w-[300px]">
        <div className="border-2 border-black rounded p-4">
          <h2 className='font-bold uppercase mb-2'>{name}</h2>
          <h4 className="flex items-center justify-between gap-4">Created in slot: <span>{slot}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Transaction count: <span>{count}</span></h4>
          {breakdown.map(([name, bytes]) => (
            <h4 key={name} className="flex items-center justify-between gap-4">{name}: <span>{printBytes(bytes)}</span></h4>
          ))}
          <h4 className="flex items-center justify-between gap-4">Transaction size: <span>{printBytes(txBytes)}</span></h4>
          <h4 className="flex items-center justify-between gap-4">Total size: <span>{printBytes(totalBytes)}</span></h4>
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
    const breakdown: [string, number][] = [
      ["Header size", block.headerBytes],
    ];
    if (block.endorsement) {
      breakdown.push(["Certificate size", block.endorsement.bytes]);
    }
    result.set("block", {
      name: "Block",
      slot: block.slot,
      txs: block.txs,
      breakdown,
    });
    if (block.endorsement) {
      for (const ib of block.endorsement.ibs) {
        result.set(ib.id, {
          name: "Input Block",
          slot: ib.slot,
          txs: ib.txs,
          breakdown: [
            ["Header size", ib.headerBytes],
          ],
        });
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
        <div className="flex w-full h-full items-center justify-center">
          {ibs.length ? (
            <div className={cx("pr-6 border-r-2 border-black")}>
              <div className="flex flex-col gap-2">
                {ibs.map(ib => {
                  const isSelected = selected?.key === ib.id;
                  const proportion = 2 * ib.txs.length / block.txs.length;
                  return (
                    <Box key={ib.id} selected={isSelected} proportion={proportion} onClick={selectBox(ib.id)} className={classes.input}>
                      Input Block
                      <span className="text-sm">Slot {ib.slot}, {ib.txs.length} TX</span>
                    </Box>
                  );
                })}
              </div>
            </div>
          ) : null}
          {eb && (
            <div className={cx('pr-4 pl-6', classes.endorser, { [classes['has-ibs']]: ibs.length })}>
              <Box proportion={1}>
                Endorsement Block
                <span className='text-sm'>Slot {eb.slot}</span>
              </Box>
            </div>
          )}
          <div className={cx('pl-4', classes.block, { [classes['has-eb']]: !!eb })}>
            <Box selected={selected?.key === "block"} proportion={2} onClick={selectBox("block")}>
              Block
              <span className='text-sm'>Slot {block.slot}, {block.txs.length} TX</span>
            </Box>
          </div>
        </div>

      </div>
    </>
  );
}
