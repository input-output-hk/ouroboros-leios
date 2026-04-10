import assert from 'node:assert/strict';
import test from 'node:test';
import { computeFrontRunStats } from './stats.js';
import type { Block, EndorserBlock, GlobalTx } from './types.js';

test('Praos accounting keeps RB and total rates equal', () => {
  const txs: GlobalTx[] = [
    { idx: 0, txId: 'T0', size_B: 1, isAdversarial: false, honestCounterpart: -1, adversarialVariant: -1, includedInBlock: -1 },
    { idx: 1, txId: 'T1', size_B: 1, isAdversarial: true, honestCounterpart: 0, adversarialVariant: -1, includedInBlock: -1 },
  ];
  const blocks: Block[] = [
    { blockId: 'B0', producer: 0, clock: 0, txIndices: [0, 1], size_B: 2, honestCount: 1, adversarialCount: 1 },
  ];
  const ebs: EndorserBlock[] = [];

  const stats = computeFrontRunStats(txs, blocks, ebs, false);

  assert.equal(stats.rbFrontRunRate, 0.5);
  assert.equal(stats.totalFrontRunRate, 0.5);
  assert.equal(stats.certifiedEBTotalTx, 0);
});

test('Leios total rate includes certified EB payload', () => {
  const txs: GlobalTx[] = [
    { idx: 0, txId: 'T0', size_B: 1, isAdversarial: false, honestCounterpart: -1, adversarialVariant: -1, includedInBlock: -1 },
    { idx: 1, txId: 'T1', size_B: 1, isAdversarial: false, honestCounterpart: -1, adversarialVariant: -1, includedInBlock: -1 },
    { idx: 2, txId: 'T2', size_B: 1, isAdversarial: true, honestCounterpart: 1, adversarialVariant: -1, includedInBlock: -1 },
  ];
  const blocks: Block[] = [
    { blockId: 'B0', producer: 0, clock: 0, txIndices: [1], size_B: 1, honestCount: 1, adversarialCount: 0 },
  ];
  const ebs: EndorserBlock[] = [
    { ebId: 'EB0', producer: 0, clock: 0, txRefs: [0, 2], size_B: 2, honestCount: 1, adversarialCount: 1, certified: true },
  ];

  const stats = computeFrontRunStats(txs, blocks, ebs, true);

  assert.equal(stats.rbFrontRunRate, 0);
  assert.equal(stats.totalAdversarialTx, 1);
  assert.equal(stats.totalTx, 3);
  assert.equal(stats.totalFrontRunRate, 1 / 3);
  assert.ok(stats.totalFrontRunRate >= stats.rbFrontRunRate);
});
