import { ISimulationBlock, ISimulationTransaction } from '@/contexts/SimContext/types';
import { printBytes } from '@/utils';
import Highcharts from 'highcharts';
import HighchartsReact from 'highcharts-react-official';
import { FC, useMemo, useState } from "react";

// highcharts modules can only load client-side
if (typeof window === 'object') {
  await import('highcharts/modules/sankey');
  await import('highcharts/modules/organization');
}

type NodeOptions = Highcharts.SeriesSankeyNodesOptionsObject & { width?: number };

export interface IBlockContentsProps {
  block: ISimulationBlock;
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
}

const Stats: FC<IStatsProps> = ({ name, slot, txs, breakdown, position: [left, top] }) => {
  const txBytes = txs?.reduce((sum, tx) => sum + tx.bytes, 0) ?? 0;
  const totalBytes = breakdown.reduce((sum, el) => sum + el[1], txBytes);
  return (
    <div className="flex flex-col items-center justify-between gap-4 z-10 absolute" style={{ left, top }}>
      <div className="flex flex-col gap-4 backdrop-blur-sm bg-white/80 text-xl min-w-[300px]">
        <div className="border-2 border-black rounded p-4">
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
  const allTxs = useMemo(() => {
    const txs = new Set<number>();
    for (const tx of block.txs) {
      txs.add(tx.id);
    }
    for (const ib of block.cert?.eb.ibs ?? []) {
      for (const tx of ib.txs) {
        txs.add(tx.id);
      }
    }
    return txs;
  }, [block])
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

  const options = useMemo(() => {
    const eb = block.cert?.eb;
    const ibs = block.cert?.eb?.ibs ?? [];

    const nodes: NodeOptions[] = [
      {
        id: 'block',
        name: 'Block',
        title: `Slot ${block.slot}, ${block.txs.length} TX(s)`,
        width: 200,
        height: 100,
      }
    ];
    const edges: Highcharts.SeriesSankeyPointOptionsObject[] = [
      { from: 'block' },
    ];

    if (eb) {
      nodes.push({
        id: 'eb',
        name: 'Endorsement Block',
        title: `Slot ${eb.slot}`,
        width: 200,
      });
      edges.push({ from: 'block', to: 'eb' });
    }

    for (const ib of ibs) {
      const node: NodeOptions = {
        id: ib.id,
        name: 'Input Block',
        title: `Slot ${ib.slot}, ${ib.txs.length} TX(s)`,
        height: Math.max(50, 100 * Math.min(ib.txs.length / block.txs.length, 200)),
      };
      if (ibs.length <= 3) {
        node.width = 200;
      }
      nodes.push(node);
      edges.push({ from: 'eb', to: ib.id });
    }

    const series: Highcharts.SeriesOrganizationOptions = {
      type: 'organization',
      data: edges,
      levels: [
        {
          level: 0,
          color: '#8884d8'
        },
        {
          level: 1,
          color: '#cccccc'
        },
        {
          level: 2,
          color: '#82ca9d'
        }
      ],
      nodes,
      colorByPoint: false,
      nodeWidth: 100,
      events: {
        click(event: any) {
          const id = event.point.id as string;
          event.stopPropagation();
          setSelected({
            key: id,
            position: [event.pageX, event.pageY],
          });
        }
      }
    };

    const title = 'Block Transactions';
    const subtitle = allTxs.size === 1 ? `1 transaction` : `${allTxs.size} transactions`;
    const options: Highcharts.Options = {
      chart: {
        inverted: true,
        width: 640,
        height: 500,
        events: {
          click() {
            setSelected(null);
          }
        },
      },
      title: {
        text: `<h2 class="font-bold text-xl">${title}</h2><h3 class="font-bold text-l">${subtitle}</h3>`,
        useHTML: true,
      },
      tooltip: {
        enabled: false,
      },
      series: [series],
    };
    return options;
  }, [block]);


  return (
    <>
      {selected && <Stats {...stats.get(selected.key)!} position={selected.position} />}
      <HighchartsReact
        highcharts={Highcharts}
        options={options}
        allowChartUpdate={false}
      />
    </>
  );
}
