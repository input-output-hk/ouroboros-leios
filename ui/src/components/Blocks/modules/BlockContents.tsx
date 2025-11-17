import {
  ISimulationBlock,
  ISimulationEndorsementBlock,
  ISimulationInputBlock,
  ISimulationTransaction,
} from "@/contexts/SimContext/types";
import cx from "classnames";
import {
  CSSProperties,
  FC,
  MouseEvent,
  PropsWithChildren,
  ReactElement,
  useMemo,
  useState,
} from "react";

import { printBytes } from "@/utils";
import classes from "./styles.module.css";

export interface IBlockContentsProps {
  block: ISimulationBlock;
}

interface IBoxProps extends PropsWithChildren {
  className?: string;
  style?: CSSProperties;
  hovered?: boolean;
  onHover?: (e: MouseEvent) => void;
  onClick?: (e: MouseEvent) => void;
}

const Box: FC<IBoxProps> = ({
  hovered,
  onHover,
  onClick,
  children,
  className,
  style,
}) => {
  const color = hovered ? "border-black" : "border-gray-400";
  return (
    <span
      className={cx(
        "border-2 border-solid min-h-24 max-h-48 w-48 flex flex-col items-center justify-center text-center",
        color,
        { "cursor-pointer": !!onHover },
        { [classes.hovered]: hovered },
        className,
      )}
      style={style}
      onMouseEnter={onHover}
      onMouseMove={onHover}
      onClick={onClick}
    >
      {children}
    </span>
  );
};

interface ITabButtonProps {
  name: string;
  active: boolean;
  onClick: () => void;
}

const TabButton: FC<ITabButtonProps> = ({ name, active, onClick }) => {
  const color = active ? "bg-[blue]" : "bg-gray-400";
  return (
    <button
      className={`${color} text-white rounded-md px-4 py-2`}
      onClick={onClick}
    >
      {name}
    </button>
  );
};

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

const Stats: FC<IStatsProps> = ({
  name,
  slot,
  txs,
  breakdown,
  position: [left, top],
  onMouseMove,
}) => {
  const txBytes = txs?.reduce((sum, tx) => sum + tx.bytes, 0) ?? 0;
  const totalBytes = breakdown.reduce((sum, el) => sum + el[1], txBytes);
  return (
    <div
      onMouseMove={onMouseMove}
      className="flex flex-col items-center justify-between gap-4 z-10 absolute"
      style={{ left, top }}
    >
      <div className="flex flex-col gap-4 backdrop-blur-xs bg-white/80 text-xl min-w-[300px]">
        <div className="border-2 border-black rounded-sm p-4">
          <h2 className="font-bold uppercase mb-2">{name}</h2>
          <h4 className="flex items-center justify-between gap-4">
            Created in slot: <span>{slot}</span>
          </h4>
          {txs && (
            <h4 className="flex items-center justify-between gap-4">
              Transaction count: <span>{txs.length}</span>
            </h4>
          )}
          {breakdown.map(([name, bytes]) => (
            <h4 key={name} className="flex items-center justify-between gap-4">
              {name}: <span>{printBytes(bytes)}</span>
            </h4>
          ))}
          {txs && (
            <h4 className="flex items-center justify-between gap-4">
              Transaction size: <span>{printBytes(txBytes)}</span>
            </h4>
          )}
          {txs && (
            <h4 className="flex items-center justify-between gap-4">
              Total size: <span>{printBytes(totalBytes)}</span>
            </h4>
          )}
        </div>
      </div>
    </div>
  );
};

interface HoverState {
  key: string;
  position: [number, number];
}

enum ContentsView {
  Input,
  Endorser,
}

interface IBlockProps {
  block: ISimulationBlock;
  hovered: boolean;
  onHover: (e: MouseEvent) => void;
}

const Block: FC<IBlockProps> = ({ block, hovered, onHover }) => {
  return (
    <div className={classes.block}>
      <Box hovered={hovered} onHover={onHover}>
        Block
        <span className="text-sm">
          Slot {block.slot}, {block.txs.length} TX
        </span>
      </Box>
    </div>
  );
};

interface IInputBlocksProps {
  ibs: ISimulationInputBlock[];
  block: ISimulationBlock;
  hovered: HoverState | null;
  onHover: (box: string | null) => (e: MouseEvent) => void;
}

const InputBlocksList: FC<IInputBlocksProps> = ({
  ibs,
  hovered,
  block,
  onHover,
}) => {
  return (
    <div
      className={cx(
        "border-2 p-[25px] border-black max-w-[80vw] overflow-scroll",
      )}
    >
      <div className="flex gap-2">
        {ibs.map((ib) => {
          const isHovered = hovered?.key === ib.id;
          const proportion = Math.min(
            100,
            (ib.txs.length * 1000) / block.txs.length,
          );
          return (
            <Box
              key={ib.id}
              style={{
                backgroundColor: `color-mix(in hsl, white, #82ca9d ${proportion}%)`,
              }}
              hovered={isHovered}
              onHover={onHover(ib.id)}
              className={classes.input}
            >
              {isHovered ? <>Input&nbsp;Block</> : "IB"}
              <span className="text-sm">
                Pipeline&nbsp;{ib.pipeline}, Slot&nbsp;{ib.slot},{" "}
                {ib.txs.length}&nbsp;TX
              </span>
            </Box>
          );
        })}
      </div>
    </div>
  );
};

interface IEndorserBlockProps {
  eb: ISimulationEndorsementBlock;
  hovered: boolean;
  onHover: (e: MouseEvent) => void;
  onClick?: (e: MouseEvent) => void;
}

const EndorserBlock: FC<IEndorserBlockProps> = ({
  eb,
  hovered,
  onHover,
  onClick,
}) => {
  return (
    <div className={classes.endorser}>
      <Box hovered={hovered} onHover={onHover} onClick={onClick}>
        Endorser Block
        <span className="text-sm">
          Pipeline {eb.pipeline}, Slot {eb.slot}
        </span>
        {eb.txs.length ? (
          <span className="text-sm">References {eb.txs.length} TX(s)</span>
        ) : null}
        {eb.ibs.length ? (
          <span className="text-sm">References {eb.ibs.length} IB(s)</span>
        ) : null}
        {eb.ebs.length ? (
          <span className="text-sm">References {eb.ebs.length} EB(s)</span>
        ) : null}
      </Box>
    </div>
  );
};

interface IEndorserBlocksProps {
  ebs: ISimulationEndorsementBlock[];
  hovered: HoverState | null;
  onHover: (box: string | null) => (e: MouseEvent) => void;
  onClick: (eb: ISimulationEndorsementBlock) => (e: MouseEvent) => void;
}

const EndorserBlocksList: FC<IEndorserBlocksProps> = ({
  ebs,
  hovered,
  onHover,
  onClick,
}) => {
  return (
    <div
      className={cx(
        "border-2 p-[25px] border-black max-w-[80vw] overflow-scroll",
      )}
    >
      <div className="flex gap-2">
        {ebs.map((eb) => {
          return (
            <EndorserBlock
              key={eb.id}
              eb={eb}
              hovered={hovered?.key == eb.id}
              onHover={onHover(eb.id)}
              onClick={onClick(eb)}
            />
          );
        })}
      </div>
    </div>
  );
};

export const BlockContents: FC<IBlockContentsProps> = ({ block }) => {
  const stats = useMemo(() => {
    const result: Map<string, ITXStats> = new Map();
    const breakdown: [string, number][] = [["Header size", block.headerBytes]];
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
      const ebs = [block.cert.eb];
      while (ebs.length) {
        const eb = ebs.pop()!;
        result.set(eb.id, {
          name: "Endorser Block",
          slot: eb.slot,
          txs: null,
          breakdown: [["Size", eb.bytes]],
        });
        for (const ib of eb.ibs) {
          result.set(ib.id, {
            name: "Input Block",
            slot: ib.slot,
            txs: ib.txs,
            breakdown: [["Header size", ib.headerBytes]],
          });
        }
        for (const nestedEb of eb.ebs) {
          ebs.push(nestedEb);
        }
      }
    }
    return result;
  }, [block]);

  const [hovered, setHovered] = useState<HoverState | null>(null);
  const [viewing, setViewing] = useState(ContentsView.Input);
  const [ebTrail, setEbTrail] = useState(block.cert?.eb ? [block.cert.eb] : []);

  const onHover = (box: string | null) => (e: MouseEvent) => {
    e.stopPropagation();
    if (box) {
      setHovered({
        key: box,
        position: [e.pageX, e.pageY],
      });
    } else {
      setHovered(null);
    }
  };

  const viewParentEb = () => {
    setEbTrail((trail) => trail.slice(1));
  };
  const viewChildEb = (eb: ISimulationEndorsementBlock) => () => {
    setEbTrail((trail) => [eb, ...trail]);
  };

  const eb: ISimulationEndorsementBlock | undefined = ebTrail[0];
  const ibs = eb?.ibs ?? [];
  const ebs = eb?.ebs ?? [];

  const parent = ebTrail[1];
  const topRow = parent ? (
    <EndorserBlock
      eb={parent}
      hovered={hovered?.key == parent.id}
      onHover={onHover(parent.id)}
      onClick={viewParentEb}
    />
  ) : (
    <Block
      block={block}
      hovered={hovered?.key == "block"}
      onHover={onHover("block")}
    />
  );

  let bottomRow: ReactElement | null = null;
  if (viewing == ContentsView.Input && ibs.length) {
    bottomRow = (
      <InputBlocksList
        ibs={ibs}
        block={block}
        hovered={hovered}
        onHover={onHover}
      />
    );
  }
  if (viewing == ContentsView.Endorser && ebs.length) {
    bottomRow = (
      <EndorserBlocksList
        ebs={ebs}
        hovered={hovered}
        onHover={onHover}
        onClick={viewChildEb}
      />
    );
  }

  return (
    <>
      {hovered && (
        <Stats
          {...stats.get(hovered.key)!}
          position={hovered.position}
          onMouseMove={onHover(hovered.key)}
        />
      )}

      <div
        className="flex flex-col w-full h-3/5 items-center"
        onMouseMove={onHover(null)}
      >
        <h2 className="font-bold text-xl">Block Transactions</h2>
        <div className="flex flex-col w-full h-full items-center justify-center">
          {topRow}
          {eb && <span className="flex flex-none w-[2px] h-[50px] bg-black" />}
          {eb && (
            <div className="flex gap-4 items-center">
              <TabButton
                name="View IB(s)"
                active={viewing == ContentsView.Input}
                onClick={() => setViewing(ContentsView.Input)}
              />
              <EndorserBlock
                eb={eb}
                hovered={hovered?.key == eb.id}
                onHover={onHover(eb.id)}
              />
              <TabButton
                name="View EB(s)"
                active={viewing == ContentsView.Endorser}
                onClick={() => setViewing(ContentsView.Endorser)}
              />
            </div>
          )}
          {bottomRow ? (
            <>
              <span className="flex flex-none w-[2px] h-[50px] bg-black" />
              {bottomRow}
            </>
          ) : null}
        </div>
      </div>
    </>
  );
};
