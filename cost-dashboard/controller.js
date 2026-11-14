// Linear Leios (CIP-164) cost estimator
// See docs/cost-estimate/ for methodology and cross-checks.

var Controller = (function() {
  'use strict'

  var GiB = 1024 * 1024 * 1024            //  B/GiB
  var T_month = 365.24 / 12 * 24 * 3600   //  s/month = 2,629,728

  // Updated 2026-11 (docs/cost-estimate/README.md, "November 2026 update")
  var MAINNET_RB_BODY = 90112             //  B: mainnet maxBlockBodySize today
  var MAINNET_TXKBPS = MAINNET_RB_BODY * 0.05 / 1000   //  TxkB/s: mainnet capacity today (f = 0.05, 1 s slots), the "× mainnet" yardstick

  // Fixed values, shown read-only: formats and benchmarks, not settings of the system
  var RB_HEADER_SIZE = 1024               //  B, also announces the EB (CIP-164 has no separate EB header)
  var TX_REF_SIZE = 37                    //  B per transaction reference in an EB body: 32 B hash + the Tx size, measured
                                          //  on every EB of two P&T cluster runs (2026-11-06 a0c13, 2026-11-09 2a1ad)
  var VOTE_SIZE = 91                      //  B: 88 B vote (consensus golden test) + 3 B MsgLeiosVotes framing
  var TX_APPLY_MS = 0.6201                //  ms/tx: full validation at mempool ingestion, mainnet mean (OLS on mainnet Apply data)
  var EB_HEADER_VAL_MS = 0.4438           //  ms per header: db-analyser empty-block statistics
  var VOTE_VAL_MS = 0.67                  //  ms per vote: one BLS signature check
  var CERT_FIXED = 54                     //  B: certificate = 54 B + 1 bit per seat (75 B on MusashiNet, 21 B bitfield)
  var CERT_VAL_BASE = 0.9                 //  ms: certificate validation = 0.9 ms + 1.9 µs per seat (Haskell verifyLeiosCert)
  var CERT_VAL_PER_SEAT = 0.0019          //  ms/seat
  var MIN_TX_SIZE = 200                   //  B: about the smallest possible transaction, the floor for the average
  var OUTBOUND_PEERS = 25                 //  upstream peers per node
  // Reapply model (CIP-164 configuration: eb-body-validation-cpu-time-ms-*)
  var REAPPLY_CONST_MS = 0.3539           //  ms per EB
  var REAPPLY_PER_BYTE_MS = 0.00002151    //  ms/B
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

    //  CPU (ms/s per node)
    var cpu = {
      apply:    txPerSec * TX_APPLY_MS,               //  full validation at mempool ingestion
      reapply:  leios ? ebRate * REAPPLY_CONST_MS + REAPPLY_PER_BYTE_MS * B : 0,   //  EB body validation
      ebHeader: p.rbRate * EB_HEADER_VAL_MS,          //  EB/RB header validation
      vote:     p.seats * ebRate * VOTE_VAL_MS,       //  one BLS check per vote
      cert:     rCert * p.certValMs                   //  certificate validation, one per certified EB
    }
    cpu.total = cpu.apply + cpu.reapply + cpu.ebHeader + cpu.vote + cpu.cert

    //  New chain data (GiB/month per node). Only confirmed data is persisted: every transaction
    //  once, and the bodies of certified EBs, which reference only the transactions RBs don't
    //  carry. Votes are ephemeral.
    var storageMonthly = (B                                         //  tx closure data
      + rCert * txsPerEb * TX_REF_SIZE                              //  certified EB bodies (tx references)
      + p.rbRate * RB_HEADER_SIZE + rCert * p.certSize) * T_month / GiB   //  RB headers (they announce the EBs) + certs

    //  Egress (GiB/month per relay):
    //  - Txs: 1 effective peer (fetch-from-one)
    //  - votes: pushed once to every downstream peer, the one it came from included (consensus PR #2430)
    //  - EB bodies (tx refs): every announced EB, certified or not; ebFetchPeers
    //  - RB/EB headers: pushed to every downstream peer
    //  - RB bodies: certificates, and the transactions RBs carry; rbFetchPeers. While Leios is
    //    active, every RB without a certificate is full (as in the capacity), so its transactions
    //    are sent again in its body, as in Praos
    var rbTxBytes = leios ? (1 - p.pCert) * p.rbRate * p.maxRbBody : B   //  B/s of transactions in RB bodies
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

    return { txkBps: txkBps, txPerSec: txPerSec, leios: leios, cpu: cpu, txsPerEb: txsPerEb,
             storageMonthly: storageMonthly, egressMonthly: egressMonthly, iops: iops }
  }

  // ================================================================
  //  A load profile: a peak phase for a share of the time, a rest phase otherwise
  // ================================================================
  //
  //  Provisioned for the peak: vCPU, IOPS and peak bandwidth. Billed on the average: egress
  //  and chain growth.

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

    //  vCPU: at least 2 per node, more if the peak with headroom needs it
    r.coresNeeded = headroom * hi.cpu.total / 1000    //  per node
    r.vcpu = nodes * Math.max(2, Math.ceil(r.coresNeeded))
    r.costVcpu = r.vcpu * getFloat(uiVcpu)

    //  Disk: the chain today plus a year of growth at the average load
    var compression = 1 - getFloat(uiCompression) / 100
    r.chainGrowth = compression * mix(hi.storageMonthly, lo.storageMonthly)   //  GiB/month per node
    r.bulk = nodes * (getFloat(uiCurrentChain) + r.chainGrowth * 12)          //  GiB after a year
    r.costStorage = r.bulk * getFloat(uiStorage)

    //  Egress on the average; peak bandwidth per relay at the peak
    r.egress = relays * mix(hi.egressMonthly, lo.egressMonthly)
    r.costEgress = r.egress * getFloat(uiEgress)
    r.nic = headroom * hi.egressMonthly * GiB / T_month * 8 / 1e6   //  Mb/s

    //  IOPS at the peak
    r.iops = headroom * nodes * hi.iops
    r.costIops = r.iops * getFloat(uiIops)

    r.cost = r.costVcpu + r.costStorage + r.costIops + r.costEgress
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
    uiTxApply.innerText = TX_APPLY_MS; uiEbHeaderVal.innerText = EB_HEADER_VAL_MS; uiVoteVal.innerText = VOTE_VAL_MS
    uiCertVal.innerText = p.certValMs.toFixed(2)

    // CPU per node, at the peak
    var cpu = r.hi.cpu
    uiCpuApply.innerText    = cpu.apply.toFixed(2)
    uiCpuReapply.innerText  = cpu.reapply.toFixed(2)
    uiCpuEbHeader.innerText = cpu.ebHeader.toFixed(3)
    uiCpuVote.innerText     = cpu.vote.toFixed(1)
    uiCpuCert.innerText     = cpu.cert.toFixed(2)
    uiCpuTotal.innerText    = cpu.total.toFixed(1)
    uiCpuPercent.innerText  = (cpu.total / 10).toFixed(1)

    // Resources and costs, all nodes
    // All nodes, with the share of one node (or relay) in brackets
    var per = function(v, n, d, who) { return n > 0 ? ' (' + (v / n).toFixed(v / n >= 100 ? 0 : d) + '/' + who + ')' : '' }
    var perNode = function(v, d) { return per(v, r.nodes, d, 'node') }
    var perRelay = function(v, d) { return per(v, r.relays, d, 'relay') }
    var chainGrowth = r.chainGrowth * r.nodes, nic = r.nic * r.relays
    uiTotalVcpu.innerText = r.vcpu;                      uiTotalVcpuUnit.innerText = 'vCPU' + perNode(r.vcpu, 0)
    uiChainGrowth.innerText = chainGrowth.toFixed(2);    uiChainGrowthUnit.innerText = 'GiB/mo' + perNode(chainGrowth, 2)
    uiTotalStorage.innerText = r.bulk.toFixed(2);        uiTotalStorageUnit.innerText = 'GiB' + perNode(r.bulk, 1)
    uiTotalIops.innerText = Math.round(r.iops);          uiTotalIopsUnit.innerText = 'IOPS' + perNode(r.iops, 0)
    uiTotalEgress.innerText = r.egress.toFixed(2);       uiTotalEgressUnit.innerText = 'GiB/mo' + perRelay(r.egress, 1)
    uiNic.innerText = nic.toFixed(1);                    uiNicUnit.innerText = 'Mb/s' + perRelay(nic, 1)
    uiCostVcpu.innerText = r.costVcpu.toFixed(2)
    uiCostStorage.innerText = r.costStorage.toFixed(2)
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

  // Cloud price presets
  var PRESETS = {
    Hyperscale: { uiVcpu: "20", uiStorage: "0.12", uiIops: "0.05", uiEgress: "0.09" },
    Discount:   { uiVcpu: "20", uiStorage: "0.10", uiIops: "0.00", uiEgress: "0.00" }
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
    , uiEgress
    , uiFetchMult
    , uiInboundPeers
    , uiIops
    , uiLDiff
    , uiLHdr
    , uiLVote
    , uiMaxEbRefs
    , uiMaxEbTxs
    , uiMaxRbBody
    , uiProducers
    , uiRelays
    , uiSpike
    , uiSpikeHours
    , uiStorage
    , uiSlotLength
    , uiTxSize
    , uiUtil
    , uiVcpu
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
