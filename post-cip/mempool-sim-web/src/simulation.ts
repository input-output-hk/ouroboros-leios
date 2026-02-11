import TinyQueue from 'tinyqueue';
import { LightNode } from './node.js';
import { Link } from './link.js';
import { TxRegistry } from './tx-registry.js';
import { TXID_B } from './types.js';
import type { Block, EndorserBlock, TxCacheMode } from './types.js';
import { logger } from './logger.js';

export type Event =
  | { kind: 'SubmitTx'; clock: number; nodeIdx: number; txIdx: number }
  | { kind: 'OfferTx'; clock: number; from: number; to: number; txIdx: number }
  | { kind: 'RequestTx'; clock: number; from: number; to: number; txIdx: number }
  | { kind: 'SendTx'; clock: number; from: number; to: number; txIdx: number }
  | { kind: 'ProduceBlock'; clock: number; producerIdx: number; blockSize_B: number }
  | { kind: 'DiffuseBlock'; clock: number; from: number; to: number; blockIdx: number }
  | { kind: 'ProduceEB'; clock: number; producerIdx: number; ebSize_B: number }
  | { kind: 'DiffuseEB'; clock: number; from: number; to: number; ebIdx: number }
  | { kind: 'FetchEBTx'; clock: number; from: number; to: number; txIdx: number }
  | { kind: 'SendEBTx'; clock: number; from: number; to: number; txIdx: number };

export class Simulation {
  readonly nodes: LightNode[];
  readonly registry: TxRegistry;
  readonly links: Map<string, Link>;
  private queue: TinyQueue<Event>;
  private _currentTime = 0;
  private _eventsProcessed = 0;
  readonly blocks: Block[] = [];
  readonly endorserBlocks: EndorserBlock[] = [];

  // Leios config
  ebEnabled = false;
  ebSize_B = 10_000_000;
  txCacheMode: TxCacheMode = 'mempool';

  constructor(nodes: LightNode[], links: Map<string, Link>) {
    this.nodes = nodes;
    this.registry = new TxRegistry(nodes.length);
    this.links = links;
    this.queue = new TinyQueue<Event>([], (a, b) => a.clock - b.clock);
  }

  get currentTime(): number { return this._currentTime; }
  get eventsProcessed(): number { return this._eventsProcessed; }
  get pendingEvents(): number { return this.queue.length; }

  push(event: Event): void {
    this.queue.push(event);
  }

  private getLink(from: number, to: number): Link | undefined {
    return this.links.get(`${from}-${to}`);
  }

  /**
   * Core logic for a node receiving/accepting a tx into its mempool.
   * Used by both SubmitTx and SendTx handlers.
   */
  private acceptTx(nodeIdx: number, txIdx: number, clock: number): void {
    const reg = this.registry;
    const node = this.nodes[nodeIdx]!;

    // 1. Already known?
    if (reg.known[txIdx]!.get(nodeIdx)) return;

    // 2. Conflict?
    if (reg.hasConflict(txIdx, nodeIdx)) return;

    // 3. Mark known
    reg.known[txIdx]!.set(nodeIdx);

    let activeTxIdx = txIdx;

    // 4. Adversary front-run: if node is adversary and tx is honest, create variant
    if (!node.honest && !reg.txs[txIdx]!.isAdversarial) {
      const honestTx = reg.txs[txIdx]!;
      if (honestTx.adversarialVariant < 0) {
        const advIdx = reg.register(
          honestTx.txId + 'adv',
          honestTx.size_B,
          true,
          txIdx,
        );
        honestTx.adversarialVariant = advIdx;
      }
      activeTxIdx = honestTx.adversarialVariant;
      // Mark adversarial variant known to this node
      reg.known[activeTxIdx]!.set(nodeIdx);
    }

    const tx = reg.txs[activeTxIdx]!;

    // 5. Capacity check
    if (!node.canFitTx(tx.size_B)) return;

    // 6. Add to mempool
    reg.inMempool[activeTxIdx]!.set(nodeIdx);
    node.addToMempool(tx.size_B);

    // 7. Propagate OfferTx to upstream peers
    const delay_base = node.honest ? 0 : node.frontrunDelay_s;
    for (const peerIdx of node.upstreamPeers) {
      const link = this.getLink(peerIdx, nodeIdx) ?? this.getLink(nodeIdx, peerIdx);
      if (!link) continue;
      this.push({
        kind: 'OfferTx',
        clock: link.computeDelay(clock + delay_base, TXID_B),
        from: nodeIdx,
        to: peerIdx,
        txIdx: activeTxIdx,
      });
    }
    // Also offer to downstream peers
    for (const peerIdx of node.downstreamPeers) {
      const link = this.getLink(nodeIdx, peerIdx);
      if (!link) continue;
      this.push({
        kind: 'OfferTx',
        clock: link.computeDelay(clock + delay_base, TXID_B),
        from: nodeIdx,
        to: peerIdx,
        txIdx: activeTxIdx,
      });
    }
  }

  run(): void {
    const isDebug = logger.isLevelEnabled?.('debug') ?? false;
    while (this.queue.length > 0) {
      const event = this.queue.pop()!;
      this._currentTime = event.clock;
      this._eventsProcessed++;

      switch (event.kind) {
        case 'SubmitTx':
          this.acceptTx(event.nodeIdx, event.txIdx, event.clock);
          break;

        case 'OfferTx': {
          const reg = this.registry;
          const toIdx = event.to;
          // Already in mempool?
          if (reg.inMempool[event.txIdx]!.get(toIdx)) break;
          // Conflict?
          if (reg.hasConflict(event.txIdx, toIdx)) break;
          // Schedule RequestTx back
          const linkBack = this.getLink(toIdx, event.from) ?? this.getLink(event.from, toIdx);
          if (linkBack) {
            this.push({
              kind: 'RequestTx',
              clock: linkBack.computeDelay(event.clock, TXID_B),
              from: toIdx,
              to: event.from,
              txIdx: event.txIdx,
            });
          }
          break;
        }

        case 'RequestTx': {
          const reg = this.registry;
          const responder = event.to; // node that has the tx
          // Does responder still have it?
          if (!reg.inMempool[event.txIdx]!.get(responder)) break;
          const tx = reg.txs[event.txIdx]!;
          const linkFwd = this.getLink(responder, event.from) ?? this.getLink(event.from, responder);
          if (linkFwd) {
            this.push({
              kind: 'SendTx',
              clock: linkFwd.computeDelay(event.clock, tx.size_B),
              from: responder,
              to: event.from,
              txIdx: event.txIdx,
            });
          }
          break;
        }

        case 'SendTx':
          this.acceptTx(event.to, event.txIdx, event.clock);
          break;

        case 'ProduceBlock':
          this.handleProduceBlock(event.producerIdx, event.clock, event.blockSize_B);
          break;

        case 'DiffuseBlock':
          this.handleDiffuseBlock(event.to, event.blockIdx, event.clock);
          break;

        case 'ProduceEB':
          this.handleProduceEB(event.producerIdx, event.clock, event.ebSize_B);
          break;

        case 'DiffuseEB':
          this.handleDiffuseEB(event.to, event.ebIdx, event.clock);
          break;

        case 'FetchEBTx': {
          // Node `from` requests a tx referenced in an EB from node `to`
          const reg = this.registry;
          const responder = event.to;
          if (!reg.inMempool[event.txIdx]!.get(responder) && !reg.inCache[event.txIdx]!.get(responder)) break;
          const tx = reg.txs[event.txIdx]!;
          const link = this.getLink(responder, event.from) ?? this.getLink(event.from, responder);
          if (link) {
            this.push({
              kind: 'SendEBTx',
              clock: link.computeDelay(event.clock, tx.size_B),
              from: responder,
              to: event.from,
              txIdx: event.txIdx,
            });
          }
          break;
        }

        case 'SendEBTx': {
          const reg = this.registry;
          const nodeIdx = event.to;
          const txIdx = event.txIdx;
          if (reg.known[txIdx]!.get(nodeIdx)) break;
          reg.known[txIdx]!.set(nodeIdx);

          if (this.txCacheMode === 'cache-only' || this.txCacheMode === 'both') {
            reg.inCache[txIdx]!.set(nodeIdx);
          }
          if (this.txCacheMode === 'mempool' || this.txCacheMode === 'both') {
            const node = this.nodes[nodeIdx]!;
            const tx = reg.txs[txIdx]!;
            if (node.canFitTx(tx.size_B)) {
              reg.inMempool[txIdx]!.set(nodeIdx);
              node.addToMempool(tx.size_B);
            }
          }
          break;
        }
      }
    }
  }

  private handleProduceBlock(producerIdx: number, clock: number, blockSize_B: number): void {
    const reg = this.registry;
    const producer = this.nodes[producerIdx]!;
    const blockIdx = this.blocks.length;

    // Collect txs from producer's mempool up to block size
    const txIndices: number[] = [];
    let size = 0;
    let honestCount = 0;
    let adversarialCount = 0;

    for (let i = 0; i < reg.txs.length; i++) {
      const tx = reg.txs[i]!;
      if (tx.includedInBlock >= 0) continue;
      if (!reg.inMempool[i]!.get(producerIdx)) continue;
      if (size + tx.size_B > blockSize_B) continue;
      txIndices.push(i);
      size += tx.size_B;
      if (tx.isAdversarial) adversarialCount++;
      else honestCount++;
    }

    const block: Block = {
      blockId: `B${blockIdx}`,
      producer: producerIdx,
      clock,
      txIndices,
      size_B: size,
      honestCount,
      adversarialCount,
    };
    this.blocks.push(block);

    if (logger.isLevelEnabled?.('info') ?? true) {
      logger.info({
        blockId: block.blockId,
        producer: producer.id,
        clock,
        txCount: txIndices.length,
        size_B: size,
        honestCount,
        adversarialCount,
      }, 'block produced');
    }

    // Remove included txs from ALL nodes' mempools
    for (const txIdx of txIndices) {
      const tx = reg.txs[txIdx]!;
      tx.includedInBlock = blockIdx;

      // Sweep mempool bitmap — remove from every node
      reg.inMempool[txIdx]!.forEach((nodeIdx) => {
        this.nodes[nodeIdx]!.removeFromMempool(tx.size_B);
      });
      reg.inMempool[txIdx]!.reset();

      // Also remove counterpart
      if (tx.isAdversarial && tx.honestCounterpart >= 0) {
        const cp = tx.honestCounterpart;
        const cpTx = reg.txs[cp]!;
        cpTx.includedInBlock = blockIdx; // mark as resolved
        reg.inMempool[cp]!.forEach((nodeIdx) => {
          this.nodes[nodeIdx]!.removeFromMempool(cpTx.size_B);
        });
        reg.inMempool[cp]!.reset();
      } else if (!tx.isAdversarial && tx.adversarialVariant >= 0) {
        const av = tx.adversarialVariant;
        const avTx = reg.txs[av]!;
        avTx.includedInBlock = blockIdx;
        reg.inMempool[av]!.forEach((nodeIdx) => {
          this.nodes[nodeIdx]!.removeFromMempool(avTx.size_B);
        });
        reg.inMempool[av]!.reset();
      }
    }

    // Producer marks block seen
    producer.seenBlocks.add(block.blockId);

    // Produce EB if enabled
    if (this.ebEnabled) {
      this.push({
        kind: 'ProduceEB',
        clock,
        producerIdx,
        ebSize_B: this.ebSize_B,
      });
    }

    // Diffuse block to downstream peers
    for (const peerIdx of producer.downstreamPeers) {
      const link = this.getLink(producerIdx, peerIdx);
      if (!link) continue;
      this.push({
        kind: 'DiffuseBlock',
        clock: link.computeDelay(clock, size),
        from: producerIdx,
        to: peerIdx,
        blockIdx,
      });
    }
  }

  private handleDiffuseBlock(nodeIdx: number, blockIdx: number, clock: number): void {
    const node = this.nodes[nodeIdx]!;
    const block = this.blocks[blockIdx]!;

    if (node.seenBlocks.has(block.blockId)) return;
    node.seenBlocks.add(block.blockId);

    const reg = this.registry;

    // Remove included txs from this node's mempool
    for (const txIdx of block.txIndices) {
      const tx = reg.txs[txIdx]!;
      if (reg.inMempool[txIdx]!.get(nodeIdx)) {
        reg.inMempool[txIdx]!.clear(nodeIdx);
        node.removeFromMempool(tx.size_B);
      }
      // Also counterpart
      if (tx.isAdversarial && tx.honestCounterpart >= 0) {
        const cp = tx.honestCounterpart;
        if (reg.inMempool[cp]!.get(nodeIdx)) {
          reg.inMempool[cp]!.clear(nodeIdx);
          node.removeFromMempool(reg.txs[cp]!.size_B);
        }
      } else if (!tx.isAdversarial && tx.adversarialVariant >= 0) {
        const av = tx.adversarialVariant;
        if (reg.inMempool[av]!.get(nodeIdx)) {
          reg.inMempool[av]!.clear(nodeIdx);
          node.removeFromMempool(reg.txs[av]!.size_B);
        }
      }
    }

    // Propagate to downstream peers
    for (const peerIdx of node.downstreamPeers) {
      const link = this.getLink(nodeIdx, peerIdx);
      if (!link) continue;
      this.push({
        kind: 'DiffuseBlock',
        clock: link.computeDelay(clock, block.size_B),
        from: nodeIdx,
        to: peerIdx,
        blockIdx,
      });
    }
  }

  private handleProduceEB(producerIdx: number, clock: number, ebSize_B: number): void {
    const reg = this.registry;
    const producer = this.nodes[producerIdx]!;
    const ebIdx = this.endorserBlocks.length;

    const txRefs: number[] = [];
    let size = 0;

    for (let i = 0; i < reg.txs.length; i++) {
      const tx = reg.txs[i]!;
      if (tx.includedInBlock >= 0) continue;
      if (!reg.inMempool[i]!.get(producerIdx)) continue;
      if (size + tx.size_B > ebSize_B) continue;
      txRefs.push(i);
      size += tx.size_B;
    }

    const eb: EndorserBlock = {
      ebId: `EB${ebIdx}`,
      producer: producerIdx,
      clock,
      txRefs,
      size_B: size,
    };
    this.endorserBlocks.push(eb);

    producer.seenEBs.add(eb.ebId);

    if (logger.isLevelEnabled?.('info') ?? true) {
      logger.info({
        ebId: eb.ebId,
        producer: producer.id,
        clock,
        txCount: txRefs.length,
        size_B: size,
      }, 'endorser block produced');
    }

    // Diffuse EB to downstream peers (EB header is small, use TXID_B as proxy)
    for (const peerIdx of producer.downstreamPeers) {
      const link = this.getLink(producerIdx, peerIdx);
      if (!link) continue;
      this.push({
        kind: 'DiffuseEB',
        clock: link.computeDelay(clock, TXID_B * txRefs.length),
        from: producerIdx,
        to: peerIdx,
        ebIdx,
      });
    }
  }

  private handleDiffuseEB(nodeIdx: number, ebIdx: number, clock: number): void {
    const node = this.nodes[nodeIdx]!;
    const eb = this.endorserBlocks[ebIdx]!;

    if (node.seenEBs.has(eb.ebId)) return;
    node.seenEBs.add(eb.ebId);

    const reg = this.registry;

    // For each tx in EB that this node doesn't know, fetch it
    for (const txIdx of eb.txRefs) {
      if (!reg.known[txIdx]!.get(nodeIdx)) {
        // Find a peer that has it (the EB producer or whoever diffused)
        // Use upstream peers as potential sources
        for (const peerIdx of node.upstreamPeers) {
          if (reg.inMempool[txIdx]!.get(peerIdx) || reg.inCache[txIdx]!.get(peerIdx)) {
            const link = this.getLink(peerIdx, nodeIdx) ?? this.getLink(nodeIdx, peerIdx);
            if (link) {
              this.push({
                kind: 'FetchEBTx',
                clock: link.computeDelay(clock, TXID_B),
                from: nodeIdx,
                to: peerIdx,
                txIdx,
              });
              break; // only need one source
            }
          }
        }
      }
    }

    // Propagate EB to downstream peers
    for (const peerIdx of node.downstreamPeers) {
      const link = this.getLink(nodeIdx, peerIdx);
      if (!link) continue;
      this.push({
        kind: 'DiffuseEB',
        clock: link.computeDelay(clock, TXID_B * eb.txRefs.length),
        from: nodeIdx,
        to: peerIdx,
        ebIdx,
      });
    }
  }
}
