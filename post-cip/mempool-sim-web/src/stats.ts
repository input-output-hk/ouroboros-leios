import type { Block, EndorserBlock, GlobalTx } from './types.js';

export interface FrontRunStats {
  rbHonestTx: number;
  rbAdversarialTx: number;
  rbTotalTx: number;
  certifiedEBHonestTx: number;
  certifiedEBAdversarialTx: number;
  certifiedEBTotalTx: number;
  totalHonestTx: number;
  totalAdversarialTx: number;
  totalTx: number;
  rbFrontRunRate: number;
  totalFrontRunRate: number;
}

export function computeFrontRunStats(
  txs: readonly GlobalTx[],
  blocks: readonly Block[],
  endorserBlocks: readonly EndorserBlock[],
  includeCertifiedEBPayload: boolean,
): FrontRunStats {
  const rbHonestTx = blocks.reduce((s, b) => s + b.honestCount, 0);
  const rbAdversarialTx = blocks.reduce((s, b) => s + b.adversarialCount, 0);
  const rbTotalTx = rbHonestTx + rbAdversarialTx;

  let certifiedEBHonestTx = 0;
  let certifiedEBAdversarialTx = 0;
  if (includeCertifiedEBPayload) {
    for (const eb of endorserBlocks) {
      if (!eb.certified) continue;
      for (const txIdx of eb.txRefs) {
        if (txs[txIdx]!.isAdversarial) certifiedEBAdversarialTx++;
        else certifiedEBHonestTx++;
      }
    }
  }
  const certifiedEBTotalTx = certifiedEBHonestTx + certifiedEBAdversarialTx;

  const totalHonestTx = rbHonestTx + certifiedEBHonestTx;
  const totalAdversarialTx = rbAdversarialTx + certifiedEBAdversarialTx;
  const totalTx = totalHonestTx + totalAdversarialTx;

  const rbFrontRunRate = rbTotalTx > 0 ? rbAdversarialTx / rbTotalTx : 0;
  const totalFrontRunRate = totalTx > 0 ? totalAdversarialTx / totalTx : 0;

  return {
    rbHonestTx,
    rbAdversarialTx,
    rbTotalTx,
    certifiedEBHonestTx,
    certifiedEBAdversarialTx,
    certifiedEBTotalTx,
    totalHonestTx,
    totalAdversarialTx,
    totalTx,
    rbFrontRunRate,
    totalFrontRunRate,
  };
}
