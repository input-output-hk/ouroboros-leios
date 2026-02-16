import TinyQueue from 'tinyqueue';
import { LightNode } from './node.js';
import { Link } from './link.js';
import { TxRegistry } from './tx-registry.js';
import { TXID_B } from './types.js';
import type { Block, EndorserBlock } from './types.js';
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
  | { kind: 'SendEBTx'; clock: number; from: number; to: number; txIdx: number }
  | { kind: 'PeerChurn'; clock: number };

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
  ebAnnouncementRate = 1.0;
  ebCertificationRate = 1.0;
  private lastEB: EndorserBlock | null = null;

  // Peer churn config
  peerChurnEnabled = false;
  peerChurnInterval_s = 5;
  peerChurnRate = 0.05;

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

  /** Process a single event (extracted from run loop for reuse by step()). */
  private processEvent(event: Event): void {
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
        if (!reg.inMempool[event.txIdx]!.get(responder)) break;
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

      case 'SendEBTx':
        // EB-fetched txs enter the mempool via the normal acceptTx path,
        // creating backpressure that defends against adversary front-running
        this.acceptTx(event.to, event.txIdx, event.clock);
        break;

      case 'PeerChurn':
        this.handlePeerChurn(event.clock);
        break;
    }
  }

  run(): void {
    while (this.queue.length > 0) {
      const event = this.queue.pop()!;
      this._currentTime = event.clock;
      this._eventsProcessed++;
      this.processEvent(event);
    }
  }

  /** Process one event and return it (for viz stepping). Returns null if queue empty. */
  step(): Event | null {
    if (this.queue.length === 0) return null;
    const event = this.queue.pop()!;
    this._currentTime = event.clock;
    this._eventsProcessed++;
    this.processEvent(event);
    return event;
  }

  // --- Visual query helpers (for small viz scale) ---

  getNodeFillPercent(nodeIdx: number): number {
    const node = this.nodes[nodeIdx]!;
    return (node.mempoolBytes / node.mempoolCapacity_B) * 100;
  }

  getNodeTxCount(nodeIdx: number): number {
    const reg = this.registry;
    let count = 0;
    for (let i = 0; i < reg.txs.length; i++) {
      if (reg.inMempool[i]!.get(nodeIdx)) count++;
    }
    return count;
  }

  isNodePoisoned(nodeIdx: number): boolean {
    const reg = this.registry;
    for (let i = 0; i < reg.txs.length; i++) {
      if (reg.txs[i]!.isAdversarial && reg.inMempool[i]!.get(nodeIdx)) return true;
    }
    return false;
  }

  // --- Convenience methods for viz setup ---

  submitTx(clock: number, nodeIdx: number, txId: string, size_B: number): number {
    const txIdx = this.registry.register(txId, size_B, false, -1);
    this.push({ kind: 'SubmitTx', clock, nodeIdx, txIdx });
    return txIdx;
  }

  produceBlock(clock: number, producerIdx: number, blockSize_B: number): void {
    this.push({ kind: 'ProduceBlock', clock, producerIdx, blockSize_B });
  }

  private handleProduceBlock(producerIdx: number, clock: number, blockSize_B: number): void {
    const reg = this.registry;
    const producer = this.nodes[producerIdx]!;
    const blockIdx = this.blocks.length;

    // When ebEnabled: only the block IMMEDIATELY after an uncertified EB is empty
    const canIncludeTxs = !this.ebEnabled || !this.lastEB || this.lastEB.certified;
    if (this.lastEB && !this.lastEB.certified) {
      this.lastEB = null; // clear so only ONE empty block per uncertified EB
    }

    // Collect txs from producer's mempool up to block size
    const txIndices: number[] = [];
    let size = 0;
    let honestCount = 0;
    let adversarialCount = 0;

    if (canIncludeTxs) {
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

    // Produce EB if enabled (probabilistic announcement)
    if (this.ebEnabled && Math.random() < this.ebAnnouncementRate) {
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
      certified: Math.random() < this.ebCertificationRate,
    };
    this.endorserBlocks.push(eb);
    this.lastEB = eb;

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

    // Fetch unknown txs referenced by the EB — nodes must fetch to validate
    // before voting on certification (voting/diffusion not modeled explicitly)
    for (const txIdx of eb.txRefs) {
      if (!reg.known[txIdx]!.get(nodeIdx)) {
        // Find a peer that has it (the EB producer or whoever diffused)
        // Use upstream peers as potential sources
        for (const peerIdx of node.upstreamPeers) {
          if (reg.inMempool[txIdx]!.get(peerIdx)) {
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

  // --- Peer Churn ---

  schedulePeerChurn(startClock: number): void {
    if (this.peerChurnEnabled) {
      this.push({ kind: 'PeerChurn', clock: startClock + this.peerChurnInterval_s });
    }
  }

  private handlePeerChurn(clock: number): void {
    // Collect all edge keys
    const edgeKeys: string[] = [];
    this.links.forEach((_, key) => edgeKeys.push(key));

    // Mark edges for swap with probability peerChurnRate
    const marked: string[] = [];
    for (const key of edgeKeys) {
      if (Math.random() < this.peerChurnRate) {
        marked.push(key);
      }
    }

    // Shuffle marked edges (Fisher-Yates)
    for (let i = marked.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [marked[i], marked[j]] = [marked[j]!, marked[i]!];
    }

    // Pair them up and attempt swaps
    for (let i = 0; i + 1 < marked.length; i += 2) {
      const key1 = marked[i]!;
      const key2 = marked[i + 1]!;

      const [u, v] = key1.split('-').map(Number) as [number, number];
      const [x, y] = key2.split('-').map(Number) as [number, number];

      // Validate swap: u→v, x→y => u→y, x→v
      if (u === y || x === v) continue;           // no self-loops
      if (this.links.has(`${u}-${y}`)) continue;  // no duplicate edges
      if (this.links.has(`${x}-${v}`)) continue;

      // Perform swap in links Map
      const link1 = this.links.get(key1)!;
      const link2 = this.links.get(key2)!;
      this.links.delete(key1);
      this.links.delete(key2);
      this.links.set(`${u}-${y}`, link1);
      this.links.set(`${x}-${v}`, link2);

      // Update node peer arrays
      const nodeU = this.nodes[u]!;
      const nodeX = this.nodes[x]!;
      const nodeV = this.nodes[v]!;
      const nodeY = this.nodes[y]!;

      // Remove old downstream
      nodeU.downstreamPeers = nodeU.downstreamPeers.filter(p => p !== v);
      nodeX.downstreamPeers = nodeX.downstreamPeers.filter(p => p !== y);
      // Add new downstream
      nodeU.downstreamPeers.push(y);
      nodeX.downstreamPeers.push(v);

      // Remove old upstream
      nodeV.upstreamPeers = nodeV.upstreamPeers.filter(p => p !== u);
      nodeY.upstreamPeers = nodeY.upstreamPeers.filter(p => p !== x);
      // Add new upstream
      nodeY.upstreamPeers.push(u);
      nodeV.upstreamPeers.push(x);
    }

    // Schedule next churn
    this.push({ kind: 'PeerChurn', clock: clock + this.peerChurnInterval_s });
  }

  // --- Topology query helpers ---

  hasEdge(from: number, to: number): boolean {
    return this.links.has(`${from}-${to}`);
  }

  get honestCount(): number {
    let count = 0;
    for (const node of this.nodes) {
      if (node.honest) count++;
    }
    return count;
  }

  getNodeOrder(): number[] {
    const honest: number[] = [];
    const adversaries: number[] = [];
    for (const node of this.nodes) {
      if (node.honest) honest.push(node.idx);
      else adversaries.push(node.idx);
    }
    return [...honest, ...adversaries];
  }
}
