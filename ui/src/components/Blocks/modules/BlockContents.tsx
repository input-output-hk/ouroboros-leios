import { ISimulationBlock, ISimulationTransaction } from '@/contexts/SimContext/types';
import cx from "classnames";
import { CSSProperties, FC, MouseEvent, PropsWithChildren, useMemo, useState } from "react";

import { printBytes } from '@/utils';
import classes from "./styles.module.css";

export interface IBlockContentsProps {
  block: ISimulationBlock;
}

interface IBoxProps extends PropsWithChildren {
  className?: string;
  style?: CSSProperties;
  selected?: boolean;
  select?: (e: MouseEvent) => void;
}

const Box: FC<IBoxProps> = ({ selected, select, children, className, style }) => {
  const color = selected ? "border-black" : "border-gray-400";
  return (
    <span className={cx("border-2 border-solid min-h-24 max-h-48 w-48 flex flex-col items-center justify-center text-center", color, { 'cursor-pointer': !!select }, { [classes.selected]: selected }, className)} style={style}
      onMouseEnter={select}
      onMouseMove={select} >
      {children}
    </span >
  )
}

interface ITXStats {
  name: string;
  slot: number;
  txs: ISimulationTransaction[] | null;
  breakdown: [string, number][];
}

interface IStatsProps {
  name: string;
  slot: number;
  txs: ISimulationTransaction[] | null;
  breakdown: [string, number][];
  position: [number, number];
  onMouseMove: (event: MouseEvent) => void;
}

const Stats: FC<IStatsProps> = ({ name, slot, txs, breakdown, position: [left, top], onMouseMove }) => {
  const txBytes = txs?.reduce((sum, tx) => sum + tx.bytes, 0) ?? 0;
  const totalBytes = breakdown.reduce((sum, el) => sum + el[1], txBytes);
  return (
    <div onMouseMove={onMouseMove} className="flex flex-col items-center justify-between gap-4 z-10 absolute" style={{ left, top }}>
      <div className="flex flex-col gap-4 backdrop-blur-xs bg-white/80 text-xl min-w-[300px]">
        <div className="border-2 border-black rounded-sm p-4">
          <h2 className='font-bold uppercase mb-2'>{name}</h2>
          <h4 className="flex items-center justify-between gap-4">Created in slot: <span>{slot}</span></h4>
          {txs && <h4 className="flex items-center justify-between gap-4">Transaction count: <span>{txs.length}</span></h4>}
          {breakdown.map(([name, bytes]) => (
            <h4 key={name} className="flex items-center justify-between gap-4">{name}: <span>{printBytes(bytes)}</span></h4>
          ))}
          {txs && <h4 className="flex items-center justify-between gap-4">Transaction size: <span>{printBytes(txBytes)}</span></h4>}
          {txs && <h4 className="flex items-center justify-between gap-4">Total size: <span>{printBytes(totalBytes)}</span></h4>}
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
    if (block.cert) {
      breakdown.push(["Certificate size", block.cert.bytes]);
    }
    result.set("block", {
      name: "Block",
      slot: block.slot,
      txs: block.txs,
      breakdown,
    });
    if (block.cert) {
      result.set("eb", {
        name: "Endorsement Block",
        slot: block.cert.eb.slot,
        txs: null,
        breakdown: [["Size", block.cert.eb.bytes]],
      });
      for (const ib of block.cert.eb.ibs) {
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

  const eb = block.cert?.eb;
  const ibs = block.cert?.eb?.ibs ?? [];

  return (
    <>
      {selected && <Stats {...stats.get(selected.key)!} position={selected.position} onMouseMove={selectBox(selected.key)} />}

      <div className='flex flex-col w-full h-3/5 items-center' onMouseMove={selectBox(null)}>
        <h2 className='font-bold text-xl'>Block Transactions</h2>
        <div className="flex flex-col w-full h-full items-center justify-center">
          <div className={classes.block}>
            <Box selected={selected?.key === "block"} select={selectBox("block")}>
              Block
              <span className='text-sm'>Slot {block.slot}, {block.txs.length} TX</span>
            </Box>
          </div>
          {eb && (<span className="flex flex-none w-[2px] h-[50px] bg-black" />)}
          {eb && (
            <div className={classes.endorser}>
              <Box selected={selected?.key === "eb"} select={selectBox("eb")}>
                Endorsement Block
                <span className='text-sm'>Slot {eb.slot}</span>
              </Box>
            </div>
          )}
          {ibs.length ? <>
            <span className="flex flex-none w-[2px] h-[25px] bg-black" />
            <div className={cx("border-2 p-[25px] border-black max-w-[80vw] overflow-scroll")}>
              <div className="flex gap-2">
                {ibs.map(ib => {
                  const isSelected = selected?.key === ib.id;
                  const proportion = Math.min(100, ib.txs.length * 1000 / block.txs.length);
                  return (
                    <Box key={ib.id} style={{ backgroundColor: `color-mix(in hsl, white, #82ca9d ${proportion}%)` }} selected={isSelected} select={selectBox(ib.id)} className={classes.input}>
                      {isSelected ? 'Input Block' : 'IB'}
                      <span className="text-sm">Slot&nbsp;{ib.slot}, {ib.txs.length}&nbsp;TX</span>
                    </Box>
                  );
                })}
              </div>
            </div>
          </> : null}
        </div>
      </div>
    </>
  );
}
