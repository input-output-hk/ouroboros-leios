// Linear Leios (CIP-164) cost estimator
// See docs/cost-estimate/ for methodology and cross-checks.

var Controller = (function() {
  'use strict'

  var GiB = 1024 * 1024 * 1024            //  B/GiB
  var GB_PER_GIB = GiB / 1e9              //  1.073741824: volumes are in GiB, prices per GB
  var T_month = 365.24 / 12 * 24 * 3600   //  s/month = 2,629,728

  // Updated 2026-11 (docs/cost-estimate/README.md, "November 2026 update")
  var MAINNET_RB_BODY = 90112             //  B: mainnet maxBlockBodySize today
  var MAINNET_TXKBPS = MAINNET_RB_BODY * 0.05 / 1000   //  TxkB/s: mainnet capacity today (f = 0.05, 1 s slots), the "× mainnet" yardstick

  // Fixed values, shown read-only: formats and benchmarks, not settings of the system
  var RB_HEADER_SIZE = 1024               //  B, also announces the EB (CIP-164 has no separate EB header)
  var TX_REF_SIZE = 37                    //  B per transaction reference in an EB body: 32 B hash + the Tx size, measured
                                          //  on every EB of two P&T cluster runs (2026-11-06 a0c13, 2026-11-09 2a1ad)
  var VOTE_SIZE = 91                      //  B: 88 B vote (consensus golden test) + 3 B MsgLeiosVotes framing
  //  Tx apply: full validation at mempool ingestion, the mainnet mean with scripts included (OLS on
  //  mainnet Apply data). The feasibility report (ouroboros-leios PR #1156) measures no scripts: with
  //  the voting-loop fix (ouroboros-consensus 7b91f3619) 0.34–0.36 ms on c5d, 0.41 ms with two inputs;
  //  without it 0.65–3.42 ms. So 0.6201 ms covers the report's figures only if the fix is in the release.
  var TX_APPLY_MS = 0.6201                //  ms/tx
  //  Measured in the feasibility report on c5d, the oldest host class it measured (three generations old):
  //  its lowest voting-loop reading; the report's regressions give 0.19–0.21 ms
  var TX_REAPPLY_MS = 0.147               //  ms/tx: reapply of a validated Tx, voting loop (Tables 7.2b, 7.3)
  var CLOSURE_VAL_MS = 20                 //  ms per EB: fixed part of a closure validation (section 8.2)
  var EB_HEADER_VAL_MS = 0.4438           //  ms per header: db-analyser empty-block statistics
  var VOTE_VAL_MS = 0.67                  //  ms per vote: one BLS signature check
  var CERT_FIXED = 54                     //  B: certificate = 54 B + 1 bit per seat (75 B on MusashiNet, 21 B bitfield)
  var CERT_VAL_BASE = 0.9                 //  ms: certificate validation = 0.9 ms + 1.9 µs per seat (Haskell verifyLeiosCert)
  var CERT_VAL_PER_SEAT = 0.0019          //  ms/seat
  var MIN_TX_SIZE = 200                   //  B: about the smallest possible transaction, the floor for the average
  var OUTBOUND_PEERS = 25                 //  upstream peers per node
  var RAM_PER_NODE = 8                    //  GiB: LSM-backend node baseline (P&T recommendation)
  // Fast SSD = the node's volatile path (--volatile-database-path); the ImmutableDB sits on bulk disk
  // (--immutable-database-path). Measured on an LSM mainnet node, cardano-node 11.0.1 (V2LSM), 2026-11-11
  var UTXO_TABLES = 3.2                   //  GiB: UTxO set in LSM tables
  var UTXO_ENTRIES = 10.86e6              //  entries in it
  var UTXO_ENTRY_BYTES = UTXO_TABLES * GiB / UTXO_ENTRIES   //  ≈ 316 B per entry
  var TX_BYTES_PER_UTXO = 11630           //  B of Txs per net new UTxO entry: mainnet epochs 589–661 (db-sync), slope of each epoch's
                                          //  net new entries on its bytes, +85.9 per MB (the year's net is −7.9 per MB)
  var LEDGER_SNAPSHOT = 0.49              //  GiB per ledger snapshot (ledger state outside the UTxO)
  var FAST_LEDGER = 10                    //  GiB/node: needs 2 × UTxO tables + 3 snapshots (NumOfDiskSnapshots 2, plus one
                                          //  being written) + 2,160 full RBs = 8.05 GiB, rest for UTxO growth
  var K_SECURITY = 2160                   //  blocks: fetched EBs stay on the fast tier until this deep (≈ 12 h)
  var EPOCH_SLOTS = 432000                //  slots per epoch (mainnet epochLength)

  // Mainnet graduation plan (site/docs/parameter-graduation.mdx): EB references = EB txs × 40/260,
  // L_hdr fixed at 1 s, L_vote = L_diff − 3·L_hdr
  var SETS = {
    M0: { uiMaxEbTxs: 260000,  uiMaxEbRefs: 40000,  uiLHdr: 1, uiLVote: 4, uiLDiff: 7 },
    M1: { uiMaxEbTxs: 1000000, uiMaxEbRefs: 153846, uiLHdr: 1, uiLVote: 4, uiLDiff: 7 },
    M2: { uiMaxEbTxs: 3000000, uiMaxEbRefs: 461538, uiLHdr: 1, uiLVote: 4, uiLDiff: 7 }
  }
  var UTILIZATIONS = [10, 25, 50, 75, 100]

  var praosOnly = false                   //  Praos-only parameter set: Leios never deployed
  var spikes = false                      //  load: high-load hours per epoch instead of a steady utilization
  var cap = {}                            //  parameters from the last calculate(), for capacity -> EB sizing

  function getFloat(el) {
    return parseFloat(el.value)
  }

  // ================================================================
  //  Parameters
  // ================================================================

  function readParams(praos) {
    var p = {}
    p.praos = praos
    p.f = getFloat(uiASC)                             //  active slot coefficient
    p.slotRate = 1 / getFloat(uiSlotLength)           //  slot/s
    p.rbRate = p.f * p.slotRate                       //  RB/s
    p.votingWindow = Math.ceil((3 * getFloat(uiLHdr) + getFloat(uiLVote) + getFloat(uiLDiff)) * p.slotRate)   //  slots
    //  P(EB certified): the next RB comes votingWindow slots or more after the announcing one, so the
    //  votingWindow − 1 slots between have no RB (CIP-164: 0.95^13 ≈ 51%)
    p.pCert = Math.pow(1 - p.f, Math.max(0, p.votingWindow - 1))
    p.seats = getFloat(uiVotesPerEB)                  //  committee seats = votes per EB
    p.maxRbBody = getFloat(uiMaxRbBody)               //  B: maxBlockBodySize
    var txSize = getFloat(uiTxSize)
    p.txSize = txSize > MIN_TX_SIZE ? txSize : MIN_TX_SIZE   //  B/tx, the floor also when the field is empty
    p.certSize = CERT_FIXED + Math.ceil(p.seats / 8)  //  B/certificate: grows with the committee
    p.certValMs = CERT_VAL_BASE + CERT_VAL_PER_SEAT * p.seats   //  ms/cert
    p.inboundPeers = getFloat(uiInboundPeers)         //  downstream peers per relay
    p.ebFetchPeers = p.inboundPeers * getFloat(uiFetchMult) / OUTBOUND_PEERS   //  EB bodies: fetch multiplicity M
    p.rbFetchPeers = p.inboundPeers / OUTBOUND_PEERS  //  Praos blocks: BlockFetch asks one peer (MaxConcurrencyDeadline 1)
    p.epochSeconds = EPOCH_SLOTS / p.slotRate

    // Capacity: certified EBs carry up to the EB capacity, the other RBs up to the max RB body
    p.praosCap = p.rbRate * p.maxRbBody / 1000        //  TxkB/s
    var ebCapacity = Math.min(getFloat(uiMaxEbTxs), getFloat(uiMaxEbRefs) / TX_REF_SIZE * p.txSize)   //  B per EB
    p.ebCapacity = praos ? 0 : ebCapacity
    p.capacity = praos ? p.praosCap
      : Math.max(p.praosCap, p.rbRate * (p.pCert * ebCapacity + (1 - p.pCert) * p.maxRbBody) / 1000)
    p.voteWindow = getFloat(uiLVote)                  //  s: a voter validates the closure between 3·L_hdr and 3·L_hdr + L_vote
    return p
  }

  // ================================================================
  //  One load phase: per-node rates at a steady throughput
  // ================================================================

  function phase(p, txkBps) {
    var B = txkBps * 1000                             //  B/s of transactions
    var txPerSec = B / p.txSize                       //  tx/s  (1 kB = 1000 B)
    // EBs are announced only when transactions don't fit in the RB (CIP-164). Below that,
    // there are no EBs, votes or certificates, and transactions travel in RB bodies.
    var leios = !p.praos && B > p.rbRate * p.maxRbBody
    var ebRate = leios ? p.rbRate : 0                 //  EB/s announced
    var rCert = ebRate * p.pCert                      //  certified EB/s
    //  Txs in each announced EB: what certified EBs must carry beyond the RBs (as capacity), capped by the EB limits
    var ebBytes = leios ? Math.min(p.ebCapacity, Math.max(0, (B / p.rbRate - (1 - p.pCert) * p.maxRbBody) / p.pCert)) : 0
    var txsPerEb = ebBytes / p.txSize
    //  Adoption: chain selection fully validates a block it hasn't validated before (consensus
    //  ApplyVal), so Txs in RB bodies are applied again, as in Praos; a certified EB's closure is
    //  applied with ValidateNone, a reapply. RBs without a certificate carry a full body.
    var rbTxBytes = leios ? p.rbRate * (1 - p.pCert) * p.maxRbBody : B   //  B/s in RB bodies
    var ebTxBytes = Math.max(0, B - rbTxBytes)                          //  B/s in certified closures

    //  CPU (ms/s per node)
    var cpu = {
      apply:    txPerSec * TX_APPLY_MS,               //  full validation at mempool ingestion
      closure:  ebRate * (CLOSURE_VAL_MS + txsPerEb * TX_REAPPLY_MS),   //  every announced EB's closure, validated before the vote (block producers only)
      adoption: (rbTxBytes * TX_APPLY_MS + ebTxBytes * TX_REAPPLY_MS) / p.txSize,   //  block adoption
      ebHeader: p.rbRate * EB_HEADER_VAL_MS,          //  EB/RB header validation
      vote:     p.seats * ebRate * VOTE_VAL_MS,       //  one BLS check per vote
      cert:     rCert * p.certValMs                   //  certificate validation, one per certified EB
    }
    cpu.total = cpu.apply + cpu.closure + cpu.adoption + cpu.ebHeader + cpu.vote + cpu.cert

    //  One core, one EB: validating the closure with none of it in the mempool, every Tx applied (s)
    var ebValSeconds = leios ? (CLOSURE_VAL_MS + txsPerEb * TX_APPLY_MS) / 1000 : 0

    //  New chain data (GiB/month per node). Only confirmed data is persisted: every transaction
    //  once, and the bodies of certified EBs, which reference only the transactions RBs don't
    //  carry. Votes are ephemeral.
    var storageMonthly = (B                                         //  tx closure data
      + rCert * txsPerEb * TX_REF_SIZE                              //  certified EB bodies (tx references)
      + p.rbRate * RB_HEADER_SIZE + rCert * p.certSize) * T_month / GiB   //  RB headers (they announce the EBs) + certs

    //  Held on the fast SSD until K_SECURITY blocks deep (GiB/node, at this throughput sustained): the
    //  body of every fetched EB, certified or not, and the transactions of the EB closures, each once,
    //  since the LeiosDb stores a transaction's bytes once however many EBs carry it
    var ebWindow = (ebTxBytes + ebRate * txsPerEb * TX_REF_SIZE) * (K_SECURITY / p.rbRate) / GiB

    //  Egress (GiB/month per relay):
    //  - Txs: 1 effective peer (fetch-from-one)
    //  - votes: pushed once to every downstream peer, the one it came from included (consensus PR #2430)
    //  - EB bodies (tx refs): every announced EB, certified or not; ebFetchPeers
    //  - RB/EB headers: pushed to every downstream peer
    //  - RB bodies: certificates, and the transactions RBs carry; rbFetchPeers. While Leios is
    //    active, every RB without a certificate is full (as in the capacity), so its transactions
    //    are sent again in its body, as in Praos (rbTxBytes, above)
    var egressMonthly = (B
      + p.seats * VOTE_SIZE * ebRate * p.inboundPeers
      + ebRate * txsPerEb * TX_REF_SIZE * p.ebFetchPeers
      + p.rbRate * RB_HEADER_SIZE * p.inboundPeers
      + rCert * p.certSize * p.rbFetchPeers
      + rbTxBytes * p.rbFetchPeers) * T_month / GiB

    //  IOPS per node with UTxO-HD; UTxO state updates dominate (~88%)
    var ebBodyBytes = txsPerEb * TX_REF_SIZE         //  every fetched EB is written (it stays on the fast SSD)
    var iops = B / 4096 * 1.1                         //  tx data write + read-back
      + txPerSec * 3                                  //  UTxO-HD inserts/deletes
      + ebRate * Math.ceil(ebBodyBytes / 4096) * 1.2  //  EB body writes
      + p.rbRate * 2 * 1.2                            //  RB writes/reads

    return { txkBps: txkBps, txPerSec: txPerSec, leios: leios, cpu: cpu, txsPerEb: txsPerEb, ebValSeconds: ebValSeconds,
             storageMonthly: storageMonthly,
             ebWindow: ebWindow, egressMonthly: egressMonthly, iops: iops }
  }

  // ================================================================
  //  A load profile: a peak phase for a share of the time, a rest phase otherwise
  // ================================================================
  //
  //  Provisioned for the peak: vCPU, IOPS, peak bandwidth and the EBs held on the fast SSD
  //  (no more than the peak's duration of them). Billed on the average: egress, and the chain
  //  and UTxO growth that the disks grow with.

  function profile(p) {
    if (!spikes) {
      var t = Math.min(100, Math.max(0, getFloat(uiUtil) || 0)) / 100 * p.capacity   //  0 to 100% of capacity
      return { peak: t, rest: t, share: 1, peakSeconds: Infinity }
    }
    var hours = Math.max(0, getFloat(uiSpikeHours) || 0)
    return {
      peak: p.capacity,
      rest: Math.min(100, Math.max(0, getFloat(uiBaseLoad) || 0)) / 100 * p.praosCap,
      share: Math.min(1, hours * 3600 / p.epochSeconds),
      peakSeconds: hours * 3600
    }
  }

  function scenario(p, prof) {
    var hi = phase(p, prof.peak), lo = phase(p, prof.rest), w = prof.share
    var mix = function(a, b) { return w * a + (1 - w) * b }
    var r = { hi: hi, lo: lo, avgKBps: mix(hi.txkBps, lo.txkBps) }

    var headroom = getFloat(uiSpike)                //  capacity provisioned above the peak
    var producers = getFloat(uiProducers), relays = getFloat(uiRelays), nodes = producers + relays
    r.nodes = nodes; r.relays = relays

    //  vCPU: a fixed number per node, Praos and Leios alike; raised only if the peak with headroom needs more.
    //  A block producer validates every announced EB's closure before it votes; a relay doesn't vote
    r.vcpuPerNode = getFloat(uiVcpuPerNode)
    r.coresNeeded = headroom * hi.cpu.total / 1000                         //  per block producer
    var relayCores = headroom * (hi.cpu.total - hi.cpu.closure) / 1000     //  per relay
    r.vcpu = producers * Math.max(r.vcpuPerNode, Math.ceil(r.coresNeeded))
           + relays * Math.max(r.vcpuPerNode, Math.ceil(relayCores))
    r.costVcpu = r.vcpu * getFloat(uiVcpu)

    //  RAM: LSM-backend baseline on every node
    r.ram = nodes * RAM_PER_NODE
    r.costRam = r.ram * getFloat(uiRam)

    //  Disks grow with the chain: each month they hold what the node needs today plus `margin`
    //  months of growth at the average load, and are enlarged as it grows (cloud volumes resize
    //  in place). Month m holds m − 1 + margin months of growth, so the average over the first
    //  `horizon` months holds (horizon − 1) / 2 + margin.
    var margin = Math.max(0, getFloat(uiDiskMargin)), horizon = Math.max(1, getFloat(uiHorizon))

    //  Fast SSD (volatile path): FAST_LEDGER, plus UTxO growth at the average load (each new entry
    //  held twice over, like the tables), plus the EBs held at the peak
    var heldShare = Math.min(1, prof.peakSeconds / (K_SECURITY / p.rbRate))
    r.utxoGrowth = r.avgKBps * 1000 * T_month / TX_BYTES_PER_UTXO * 2 * UTXO_ENTRY_BYTES / GiB   //  GiB/month per node
    r.ebHeld = Math.max(hi.ebWindow * heldShare, lo.ebWindow)                                     //  GiB/node
    var fastAt = function(months) { return nodes * (FAST_LEDGER + r.utxoGrowth * months + r.ebHeld) }

    //  Bulk disk (immutable path): the chain today plus its growth at the average load
    var compression = 1 - getFloat(uiCompression) / 100
    r.chainGrowth = compression * mix(hi.storageMonthly, lo.storageMonthly)   //  GiB/month per node
    var bulkAt = function(months) { return nodes * (getFloat(uiCurrentChain) / GB_PER_GIB + r.chainGrowth * months) }   //  the current chain is given in GB

    var storageCost = function(months) {
      return (fastAt(months) * getFloat(uiStorageFast) + bulkAt(months) * getFloat(uiStorage)) * GB_PER_GIB
    }
    r.fast = fastAt(margin); r.bulk = bulkAt(margin)                  //  GiB, first month
    r.costStorage = storageCost((horizon - 1) / 2 + margin)           //  $/mo, average over the horizon
    r.costStorageFirst = storageCost(margin)                          //  $/mo, first month
    r.costStorageGrowth = storageCost(1) - storageCost(0)             //  $/mo added each month

    //  Egress on the average; peak bandwidth per relay at the peak
    r.egress = relays * mix(hi.egressMonthly, lo.egressMonthly)
    r.costEgress = r.egress * GB_PER_GIB * getFloat(uiEgress)
    r.nic = headroom * hi.egressMonthly * GiB / T_month * 8 / 1e6   //  Mb/s

    //  IOPS at the peak
    r.iops = headroom * nodes * hi.iops
    r.costIops = r.iops * getFloat(uiIops)

    r.cost = r.costVcpu + r.costRam + r.costStorage + r.costIops + r.costEgress
    return r
  }

  // ================================================================
  //  Page
  // ================================================================

  // The page shows the chosen parameters under the chosen load. Below the total: Praos alone
  // carrying the same demand, capped at what Praos can carry, on the same LSM node.
  function calculate() {
    var p = readParams(praosOnly)
    cap = p
    var prof = profile(p)
    var r = scenario(p, prof)

    var pb = readParams(true)
    var base = scenario(pb, { peak: Math.min(prof.peak, pb.praosCap), rest: Math.min(prof.rest, pb.praosCap),
                              share: prof.share, peakSeconds: prof.peakSeconds })

    render(p, prof, r, base)
    syncButtons()
  }

  function times(kBps) { return (kBps / MAINNET_TXKBPS).toFixed(2) + '×' }

  function render(p, prof, r, base) {
    // Protocol: capacity, an input too (see initialize)
    if (document.activeElement !== uiCapacity) uiCapacity.value = p.capacity.toFixed(2)
    if (document.activeElement !== uiCapacityX) uiCapacityX.value = (p.capacity / MAINNET_TXKBPS).toFixed(2)

    // Derived
    uiVotingWindow.innerText = p.votingWindow
    uiPcert.innerText = (p.pCert * 100).toFixed(1)
    uiPeakTp.innerText = r.hi.txkBps.toFixed(2)
    uiPeakTpUnit.innerText = 'TxkB/s, ' + times(r.hi.txkBps)
    uiAvgTp.innerText = r.avgKBps.toFixed(2)
    uiAvgTpUnit.innerText = 'TxkB/s, ' + times(r.avgKBps)
    uiTxPerSec.innerText = Math.round(r.hi.txPerSec)
    uiLeios.innerText = r.lo.leios ? 'yes'
      : r.hi.leios ? (prof.share < 1 ? +(prof.peakSeconds / 3600).toFixed(1) + ' h/epoch' : 'yes') : 'no'

    // Sizes & Validation (fixed)
    uiRbHeaderSize.innerText = RB_HEADER_SIZE
    uiTxRefSize.innerText = TX_REF_SIZE; uiVoteSize.innerText = VOTE_SIZE
    uiCertSize.innerText = p.certSize
    uiUtxoTables.innerText = UTXO_TABLES; uiLedgerSnapshot.innerText = LEDGER_SNAPSHOT
    uiTxApply.innerText = TX_APPLY_MS; uiEbHeaderVal.innerText = EB_HEADER_VAL_MS; uiVoteVal.innerText = VOTE_VAL_MS
    uiTxReapply.innerText = TX_REAPPLY_MS; uiClosureVal.innerText = CLOSURE_VAL_MS
    uiCertVal.innerText = p.certValMs.toFixed(2)

    // CPU per node, at the peak
    var cpu = r.hi.cpu
    uiCpuApply.innerText    = cpu.apply.toFixed(2)
    uiCpuClosure.innerText  = cpu.closure.toFixed(2)
    uiCpuAdoption.innerText = cpu.adoption.toFixed(2)
    uiCpuEbHeader.innerText = cpu.ebHeader.toFixed(3)
    uiCpuVote.innerText     = cpu.vote.toFixed(1)
    uiCpuCert.innerText     = cpu.cert.toFixed(2)
    uiCpuTotal.innerText    = cpu.total.toFixed(1)
    uiCpuPercent.innerText  = (cpu.total / 10).toFixed(1)
    uiVcpuNeeded.innerText  = r.coresNeeded.toFixed(2)
    uiVcpuNeededUnit.innerText = 'of ' + r.vcpuPerNode + ' vCPU'
    if (r.hi.leios) {
      uiEbVal.innerText = r.hi.ebValSeconds.toFixed(2)
      uiEbValUnit.innerText = 's of ' + p.voteWindow + ' s, ' + Math.round(r.hi.txsPerEb).toLocaleString('en-US') + ' Txs'
    } else {
      uiEbVal.innerText = 'no EBs'
      uiEbValUnit.innerText = ''
    }
    uiEbValWarn.hidden = !(r.hi.leios && r.hi.ebValSeconds > p.voteWindow)

    // Resources and costs, all nodes
    // All nodes, with the share of one node (or relay) in brackets
    var per = function(v, n, d, who) { return n > 0 ? ' (' + (v / n).toFixed(v / n >= 100 ? 0 : d) + '/' + who + ')' : '' }
    var perNode = function(v, d) { return per(v, r.nodes, d, 'node') }
    var perRelay = function(v, d) { return per(v, r.relays, d, 'relay') }
    var chainGrowth = r.chainGrowth * r.nodes, nic = r.nic * r.relays
    uiTotalVcpu.innerText = r.vcpu;                      uiTotalVcpuUnit.innerText = 'vCPU' + perNode(r.vcpu, 0)
    uiTotalRam.innerText = r.ram;                        uiTotalRamUnit.innerText = 'GiB' + perNode(r.ram, 0)
    uiFastStorage.innerText = r.fast.toFixed(2);         uiFastStorageUnit.innerText = 'GiB' + perNode(r.fast, 1) + ', +' + (r.utxoGrowth * r.nodes).toFixed(2) + '/mo'
    uiChainGrowth.innerText = chainGrowth.toFixed(2);    uiChainGrowthUnit.innerText = 'GiB/mo' + perNode(chainGrowth, 2)
    uiTotalStorage.innerText = r.bulk.toFixed(2);        uiTotalStorageUnit.innerText = 'GiB' + perNode(r.bulk, 1)
    uiTotalIops.innerText = Math.round(r.iops);          uiTotalIopsUnit.innerText = 'IOPS' + perNode(r.iops, 0)
    uiTotalEgress.innerText = r.egress.toFixed(2);       uiTotalEgressUnit.innerText = 'GiB/mo' + perRelay(r.egress, 1)
    uiNic.innerText = nic.toFixed(1);                    uiNicUnit.innerText = 'Mb/s' + perRelay(nic, 1)
    uiCostVcpu.innerText = r.costVcpu.toFixed(2)
    uiCostRam.innerText = r.costRam.toFixed(2)
    uiCostStorage.innerText = r.costStorage.toFixed(2)
    uiCostStorageUnit.innerText = '$/mo (month 1: ' + r.costStorageFirst.toFixed(2) + ', +' + r.costStorageGrowth.toFixed(2) + ' a month)'
    uiCostIops.innerText = r.costIops.toFixed(2)
    uiCostEgress.innerText = r.costEgress.toFixed(2)
    uiCost.innerText = r.cost.toFixed(2)

    // Praos-only baseline and what Leios adds over it
    uiCostPraos.innerText = base.cost.toFixed(2)
    if (r.hi.leios || r.lo.leios) {
      var added = r.cost - base.cost
      uiCostAdded.innerText = added.toFixed(2)
      uiCostAddedUnit.innerText = '$/mo, ' + (added >= 0 ? '+' : '') + Math.round(added / base.cost * 100) + '%'
    } else {
      uiCostAdded.innerText = 'idle'
      uiCostAddedUnit.innerText = ''
    }
  }

  // ================================================================
  //  Buttons: parameter sets, load, cloud prices
  // ================================================================

  function setPraos(praos) {
    praosOnly = praos
    ;[uiLHdr, uiLVote, uiLDiff, uiVotesPerEB, uiMaxEbRefs, uiMaxEbTxs, uiCapacity, uiCapacityX]
      .forEach(function(el) { el.disabled = praos })
    uiCostPraosRow.hidden = praos
    uiCostAddedRow.hidden = praos
  }

  function applySet(name) {
    if (name === "Praos") setPraos(true)
    else {
      setPraos(false)
      var values = SETS[name]
      if (values) for (var id in values) document.getElementById(id).value = values[id]
    }
    calculate()
  }

  function setUtilization(u) {
    spikes = false
    uiUtil.value = u
    calculate()
  }

  function setSpikes() {
    spikes = true
    calculate()
  }

  // Prices checked 2026-11-10: each preset value is the average of the on-demand list prices of
  // AWS, GCP and Azure (hyperscale) or DigitalOcean, Akamai and Hetzner (discount). Disk prices
  // are per GB: AWS EBS, Azure managed disks and DigitalOcean volumes bill per GiB, so their
  // prices are divided by 1.074 first (units checked 2026-11-14). IOPS and discount egress are
  // the average of what a node pays: 0, because every one of those plans includes more than a
  // node uses. Min, average and max per price: docs/cost-estimate/README.md, "November 2026 update".
  var PRESETS = {
    Hyperscale: {
      uiVcpu:        "22.74",   //  15.92 (GCP E2) – 26.80 (AWS)
      uiRam:         "2.23",    //  1.90 (Azure) – 2.66 (AWS)
      uiStorageFast: "0.0831",  //  per GB: 0.0745 (AWS gp3, 0.080/GiB) – 0.100 (GCP pd-balanced)
      uiStorage:     "0.0397",  //  per GB: 0.0373 (Azure, 0.040/GiB) – 0.0419 (AWS st1, 0.045/GiB)
      uiIops:        "0.00",    //  3,000 IOPS included per volume; a node uses fewer
      uiEgress:      "0.099"    //  0.087 (Azure) – 0.120 (GCP Premium)
    },
    Discount: {
      uiVcpu:        "22.86",   //  17.42 (Hetzner) – 30.71 (Akamai)
      uiRam:         "2.53",    //  1.74 (Hetzner) – 3.07 (Akamai)
      uiStorageFast: "0.00",    //  the plan's local disk at all three
      uiStorage:     "0.0857",  //  per GB: 0.064 (Hetzner) – 0.10 (Akamai); DigitalOcean 0.10/GiB = 0.093/GB
      uiIops:        "0.00",    //  not billed
      uiEgress:      "0.00"     //  12–60 TB included per pool; a pool sends less
    }
  }

  function applyPreset(name) {
    var values = PRESETS[name]
    for (var id in values) document.getElementById(id).value = values[id]
    calculate()
  }

  function hyperscaleCosts() { applyPreset("Hyperscale") }
  function discountCosts()   { applyPreset("Discount") }

  function matches(values) {
    for (var id in values)
      if (!(Math.abs(parseFloat(document.getElementById(id).value) - parseFloat(values[id])) < 1e-9)) return false
    return true
  }

  function press(button, on) {
    button.classList.toggle("active", on)
    button.setAttribute("aria-pressed", on ? "true" : "false")
  }

  //  Highlight what is loaded: a parameter set, a load, a price preset; none once a value is edited
  function syncButtons() {
    var anySet = false
    for (var name in SETS) {
      var on = !praosOnly && matches(SETS[name])
      anySet = anySet || on
      press(document.getElementById("uiSet" + name), on)
    }
    press(uiSetPraos, praosOnly)
    press(uiSetCustom, !praosOnly && !anySet)

    UTILIZATIONS.forEach(function(u) { press(document.getElementById("uiUtil" + u), !spikes && getFloat(uiUtil) === u) })
    press(uiUtilSpikes, spikes)
    uiUtilRow.hidden = spikes
    uiSpikeHoursRow.hidden = !spikes
    uiBaseLoadRow.hidden = !spikes

    for (var preset in PRESETS) press(document.getElementById("uiPreset" + preset), matches(PRESETS[preset]))
  }

  // Capacity -> EB limits: the smallest limits that carry the capacity, with references balanced
  // against Tx bytes at the average Tx size (one 37 B reference per Tx). EB bytes are rounded up
  // to whole kB after 0.005 TxkB/s of slack, so M0's 8.87 TxkB/s gives back 260 kB, and capped
  // at the field's maximum. At or below what RBs carry there are no EBs, and the limits stay as
  // they are.
  function sizeEbs(capacity) {
    var target = capacity * 1000                      //  B/s
    if (!(target > cap.rbRate * cap.maxRbBody) || !(cap.pCert > 0)) return calculate()
    var ebTxs = Math.ceil(((target - 5) / cap.rbRate - (1 - cap.pCert) * cap.maxRbBody) / cap.pCert / 1000) * 1000   //  B
    ebTxs = Math.min(ebTxs, parseFloat(uiMaxEbTxs.max) || Infinity)
    uiMaxEbTxs.value = ebTxs
    uiMaxEbRefs.value = Math.ceil(ebTxs / cap.txSize) * TX_REF_SIZE
    calculate()
  }

  function initialize() {
    [
      uiASC
    , uiBaseLoad
    , uiCompression
    , uiCurrentChain
    , uiDiskMargin
    , uiEgress
    , uiFetchMult
    , uiHorizon
    , uiInboundPeers
    , uiIops
    , uiLDiff
    , uiLHdr
    , uiLVote
    , uiMaxEbRefs
    , uiMaxEbTxs
    , uiMaxRbBody
    , uiProducers
    , uiRam
    , uiRelays
    , uiSpike
    , uiSpikeHours
    , uiStorage
    , uiSlotLength
    , uiStorageFast
    , uiTxSize
    , uiUtil
    , uiVcpu
    , uiVcpuPerNode
    , uiVotesPerEB
    ].forEach(function(el) { el.addEventListener("input", calculate) })

    // Capacity, in TxkB/s or × mainnet, sizes the EB limits; the limits set the capacity shown.
    // An ignored entry (0, empty, below Praos) snaps back on blur; one above the field's maximum
    // is taken as the maximum.
    var upTo = function(el) { return Math.min(getFloat(el), parseFloat(el.max) || Infinity) }
    uiCapacity.addEventListener("input", function() {
      var c = upTo(uiCapacity)
      if (c > 0) sizeEbs(c)
    })
    uiCapacityX.addEventListener("input", function() {
      var x = upTo(uiCapacityX)
      if (x > 0) sizeEbs(x * MAINNET_TXKBPS)
    })
    uiCapacity.addEventListener("blur", calculate)
    uiCapacityX.addEventListener("blur", calculate)

    // Tap-friendly help: clicking a label with a title toggles a help bubble
    document.addEventListener("click", function(e) {
      var label = e.target.closest("label[title]")
      var existing = document.querySelector(".help-bubble")
      var sameLabel = existing && existing._label === label

      if (existing) existing.remove()
      if (!label || sameLabel) return

      var bubble = document.createElement("div")
      bubble.className = "help-bubble"
      bubble.textContent = label.getAttribute("title")
      bubble._label = label
      label.closest(".field").after(bubble)
    })

    calculate()
  }

  return {
    calculate: calculate,
    hyperscaleCosts: hyperscaleCosts,
    discountCosts: discountCosts,
    set: applySet,
    utilization: setUtilization,
    spikes: setSpikes,
    initialize: initialize
  }

})()
