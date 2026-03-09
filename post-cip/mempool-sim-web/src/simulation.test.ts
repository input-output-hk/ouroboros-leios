import assert from 'node:assert/strict';
import test from 'node:test';
import { Link } from './link.js';
import { LightNode } from './node.js';
import { Simulation } from './simulation.js';

test('producer block selection follows local arrival order', () => {
  const honest = new LightNode(0, 'H1', true, Number.NaN, 1_500);
  const adversary = new LightNode(1, 'A1', false, 0, 1_500);

  // Fully connect two nodes.
  honest.upstreamPeers = [1];
  honest.downstreamPeers = [1];
  adversary.upstreamPeers = [0];
  adversary.downstreamPeers = [0];

  const links = new Map<string, Link>([
    ['0-1', new Link(0, 1_000_000_000)],
    ['1-0', new Link(0, 1_000_000_000)],
  ]);

  const sim = new Simulation([honest, adversary], links);

  // Register tx indices in advance so honest tx gets lower index than adversarial variant.
  const tx0 = sim.registry.register('T0', 1_500, false, -1);
  const tx1 = sim.registry.register('T1', 1_500, false, -1);

  // Adversary receives T0 first and creates T0adv, which should arrive at producer before T1.
  sim.push({ kind: 'SubmitTx', clock: 0, nodeIdx: 1, txIdx: tx0 });
  sim.push({ kind: 'SubmitTx', clock: 10, nodeIdx: 0, txIdx: tx1 });
  sim.push({ kind: 'ProduceBlock', clock: 20, producerIdx: 0, blockSize_B: 1_500 });
  sim.run();

  assert.equal(sim.blocks.length, 1);
  const block = sim.blocks[0]!;
  assert.equal(block.txIndices.length, 1);

  const advIdx = sim.registry.txs[tx0]!.adversarialVariant;
  assert.ok(advIdx >= 0, 'expected adversarial variant to be created');
  assert.equal(block.txIndices[0], advIdx);
  assert.equal(sim.registry.txs[block.txIndices[0]!]!.isAdversarial, true);

  // Included tx and counterpart must be removed from both bitmaps and ordered mempool state.
  assert.equal(honest.hasTxInOrder(tx0), false);
  assert.equal(honest.hasTxInOrder(advIdx), false);
  assert.equal(adversary.hasTxInOrder(tx0), false);
  assert.equal(adversary.hasTxInOrder(advIdx), false);
  assert.equal(sim.registry.inMempool[tx0]!.count(), 0);
  assert.equal(sim.registry.inMempool[advIdx]!.count(), 0);
});
