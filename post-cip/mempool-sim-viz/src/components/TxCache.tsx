import type { CacheTxInfo } from '@/simulation';

const COLORS = {
  background: '#200830',
  backgroundDark: '#180425',
  border: '#45364e',
  text: '#f8f6fa',
  textMuted: '#8f6dae',
  honest: '#6effd1',
  adversary: '#f97316',
  eb: '#22d3ee',
};

interface TxCacheProps {
  nodeIdx: number;
  getCache: (nodeIdx: number) => CacheTxInfo[];
  /** Changing value that triggers re-render so cache is re-read during simulation */
  tick?: number;
}

export function TxCache({ nodeIdx, getCache, tick: _ }: TxCacheProps) {
  const txs = getCache(nodeIdx);
  const totalSize = txs.reduce((s, t) => s + t.size_B, 0);

  return (
    <div className="p-3 rounded-lg" style={{ backgroundColor: COLORS.background }}>
      <div className="text-xs font-medium mb-2" style={{ color: COLORS.eb }}>
        Tx Cache ({txs.length})
      </div>

      {txs.length === 0 ? (
        <div className="text-xs py-2 text-center" style={{ color: COLORS.border }}>
          Empty
        </div>
      ) : (
        <>
          <div
            className="max-h-32 overflow-y-auto space-y-0.5 font-mono text-[10px]"
            style={{ backgroundColor: COLORS.backgroundDark, borderRadius: '4px', padding: '4px' }}
          >
            {txs.map(tx => (
              <div key={tx.txIdx} className="flex items-center gap-2 leading-tight">
                <span style={{ color: tx.isAdversarial ? COLORS.adversary : COLORS.honest }}>
                  {tx.txId}
                </span>
                <span style={{ color: COLORS.textMuted }}>
                  {tx.size_B}B
                </span>
              </div>
            ))}
          </div>
          <div className="text-[10px] mt-1 text-right font-mono" style={{ color: COLORS.textMuted }}>
            Total: {(totalSize / 1024).toFixed(1)} KB
          </div>
        </>
      )}
    </div>
  );
}
