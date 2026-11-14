// Linear Leios (CIP-164) cost estimator
// See docs/cost-estimate/ for methodology and cross-checks.

var Controller = (function() {
  'use strict'

  var GiB = 1024 * 1024 * 1024            //  B/GiB
  var T_month = 365.24 / 12 * 24 * 3600   //  s/month = 2,629,728

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
  var OUTBOUND_PEERS = 25                 //  upstream peers per node
  // Reapply model (CIP-164 configuration: eb-body-validation-cpu-time-ms-*)
  var REAPPLY_CONST_MS = 0.3539           //  ms per EB
  var REAPPLY_PER_BYTE_MS = 0.00002151    //  ms/B

  function getFloat(el) {
    return parseFloat(el.value)
  }

  function calculate() {

    // === Protocol Parameters ===

    var f = getFloat(uiASC)                          //  active slot coefficient
    var slotRate = getFloat(uiSlotRate)               //  slot/s
    var rbRate = f * slotRate                         //  RB/s
    var votingWindow = getFloat(uiVotingWindow)       //  slots
    //  P(EB certified): the next RB comes votingWindow slots or more after the announcing one, so the
    //  votingWindow − 1 slots between have no RB (CIP-164: 0.95^13 ≈ 51%)
    var pCert = Math.pow(1 - f, Math.max(0, votingWindow - 1))
    var seats = getFloat(uiVotesPerEB)                //  committee seats = votes per EB
    var maxRbBody = getFloat(uiMaxRbBody)             //  B: maxBlockBodySize
    var certSize = CERT_FIXED + Math.ceil(seats / 8)  //  B/certificate: grows with the committee
    var certValMs = CERT_VAL_BASE + CERT_VAL_PER_SEAT * seats   //  ms/cert

    uiPcert.innerText = (pCert * 100).toFixed(1)

    // === Throughput ===

    var txkBps = getFloat(uiThroughput)               //  confirmed TxkB/s
    var B = txkBps * 1000                             //  B/s of transactions
    var txSize = getFloat(uiTxSize)                   //  B/tx
    var txPerSec = B / txSize                         //  tx/s  (1 kB = 1000 B)
    uiTxPerSec.innerText = Math.round(txPerSec)

    // EBs are announced only when transactions don't fit in the RB (CIP-164). Below that,
    // there are no EBs, votes or certificates, and transactions travel in RB bodies.
    var leios = B > rbRate * maxRbBody
    var ebRate = leios ? rbRate : 0                   //  EB/s announced
    var rCert = ebRate * pCert                        //  certified EB/s
    //  Txs in each announced EB: what certified EBs must carry beyond the RBs
    var ebBytes = leios ? Math.max(0, (B / rbRate - (1 - pCert) * maxRbBody) / pCert) : 0
    var txsPerEb = ebBytes / txSize
    uiLeios.innerText = leios ? 'yes' : 'no'

    // === Network Topology ===

    var inboundPeers = getFloat(uiInboundPeers)      //  downstream peers per relay
    var ebFetchPeers = inboundPeers * getFloat(uiFetchMult) / OUTBOUND_PEERS   //  EB bodies: fetch multiplicity M
    var rbFetchPeers = inboundPeers / OUTBOUND_PEERS  //  Praos blocks: BlockFetch asks one peer (MaxConcurrencyDeadline 1)

    // === Sizes & Validation (fixed) ===

    uiRbHeaderSize.innerText = RB_HEADER_SIZE
    uiTxRefSize.innerText = TX_REF_SIZE; uiVoteSize.innerText = VOTE_SIZE
    uiCertSize.innerText = certSize
    uiTxApply.innerText = TX_APPLY_MS; uiEbHeaderVal.innerText = EB_HEADER_VAL_MS; uiVoteVal.innerText = VOTE_VAL_MS
    uiCertVal.innerText = certValMs.toFixed(2)


    // ================================================================
    //  CPU  (ms/s per node)
    // ================================================================

    var cpuApply    = txPerSec * TX_APPLY_MS                                   //  full validation at mempool ingestion
    var cpuReapply  = leios ? ebRate * REAPPLY_CONST_MS + REAPPLY_PER_BYTE_MS * B : 0   //  EB body validation
    var cpuEbHeader = rbRate * EB_HEADER_VAL_MS                                //  EB/RB header validation
    var cpuVote     = seats * ebRate * VOTE_VAL_MS                             //  one BLS check per vote
    var cpuCert     = rCert * certValMs                                        //  certificate validation, one per certified EB
    var cpuTotal    = cpuApply + cpuReapply + cpuEbHeader + cpuVote + cpuCert

    uiCpuApply.innerText    = cpuApply.toFixed(2)
    uiCpuReapply.innerText  = cpuReapply.toFixed(2)
    uiCpuEbHeader.innerText = cpuEbHeader.toFixed(3)
    uiCpuVote.innerText     = cpuVote.toFixed(1)
    uiCpuCert.innerText     = cpuCert.toFixed(2)
    uiCpuTotal.innerText    = cpuTotal.toFixed(1)
    uiCpuPercent.innerText  = (cpuTotal / 10).toFixed(1)


    // ================================================================
    //  Storage  (GiB/month per node, new data only)
    // ================================================================
    //
    //  Only confirmed data is persisted: every transaction once, and the bodies of certified
    //  EBs, which reference only the transactions RBs don't carry. Votes are ephemeral.

    var storageMonthly = (B                                         //  tx closure data
      + rCert * txsPerEb * TX_REF_SIZE                              //  certified EB bodies (tx references)
      + rbRate * RB_HEADER_SIZE + rCert * certSize) * T_month / GiB   //  RB headers (they announce the EBs) + certs


    // ================================================================
    //  Egress  (GiB/month per relay node)
    // ================================================================
    //
    //  - Txs: 1 effective peer (fetch-from-one)
    //  - votes: pushed once to every downstream peer, the one it came from included (consensus PR #2430)
    //  - EB bodies (tx refs): every announced EB, certified or not; ebFetchPeers
    //  - RB/EB headers: pushed to every downstream peer
    //  - RB bodies: certificates, and the transactions RBs carry; rbFetchPeers. While Leios is
    //    active, every RB without a certificate is full (as in the capacity), so its transactions
    //    are sent again in its body, as in Praos

    var rbTxBytes = leios ? (1 - pCert) * rbRate * maxRbBody : B   //  B/s of transactions in RB bodies
    var egressMonthly = (B
      + seats * VOTE_SIZE * ebRate * inboundPeers
      + ebRate * txsPerEb * TX_REF_SIZE * ebFetchPeers
      + rbRate * RB_HEADER_SIZE * inboundPeers
      + rCert * certSize * rbFetchPeers
      + rbTxBytes * rbFetchPeers) * T_month / GiB


    // ================================================================
    //  IOPS  (IO/s per node, with UTxO-HD)
    // ================================================================
    //
    //  UTxO state updates dominate (~88% of total).

    var ebBodyBytes = txsPerEb * TX_REF_SIZE         //  every fetched EB is written
    var iopsTotal = B / 4096 * 1.1                    //  tx data write + read-back
      + txPerSec * 3                                  //  UTxO-HD inserts/deletes
      + ebRate * Math.ceil(ebBodyBytes / 4096) * 1.2  //  EB body writes
      + rbRate * 2 * 1.2                              //  RB writes/reads


    // ================================================================
    //  Resource & Cost Aggregation  (per SPO)
    // ================================================================

    var spike     = getFloat(uiSpike)
    var producers = getFloat(uiProducers)
    var relays    = getFloat(uiRelays)
    var nodes     = producers + relays

    //  vCPU  — minimum 2 cores per node, spike-adjusted
    var cpuCoresNeeded = cpuTotal / 1000                                         //  steady-state cores
    var vcpuPerNode = Math.max(2, Math.ceil(spike * cpuCoresNeeded))
    var vcpu = nodes * vcpuPerNode
    uiTotalVcpu.innerText = vcpu
    var costVcpu = vcpu * getFloat(uiVcpu)
    uiCostVcpu.innerText = costVcpu.toFixed(2)

    //  Storage  — chain growth per month + projected total after 1 year
    var compression = 1 - getFloat(uiCompression) / 100                          //  effective ratio
    var chainGrowth = compression * storageMonthly                               //  GiB/month per node
    uiChainGrowth.innerText = chainGrowth.toFixed(2)
    var currentChain = getFloat(uiCurrentChain)                                  //  GB (current chain size)
    var storageAfter1y = nodes * (currentChain + chainGrowth * 12)               //  GiB total after 1 year
    uiTotalStorage.innerText = storageAfter1y.toFixed(2)
    var costStorage = storageAfter1y * getFloat(uiStorage)
    uiCostStorage.innerText = costStorage.toFixed(2)

    //  Network egress  — relay egress × number of relays
    var egressSPO = relays * egressMonthly                                       //  GiB/month
    uiTotalEgress.innerText = egressSPO.toFixed(2)
    var costEgress = egressSPO * getFloat(uiEgress)
    uiCostEgress.innerText = costEgress.toFixed(2)

    //  NIC  — per-relay peak bandwidth
    var perRelayBps = egressMonthly * GiB / T_month                              //  B/s steady state
    var peakMbps = spike * perRelayBps * 8 / (1000 * 1000)                       //  Mb/s peak
    uiNic.innerText = peakMbps.toFixed(1)

    //  IOPS
    var io = spike * nodes * iopsTotal
    uiTotalIops.innerText = io.toFixed(2)
    var costIops = io * getFloat(uiIops)
    uiCostIops.innerText = costIops.toFixed(2)

    //  Total
    var cost = costVcpu + costStorage + costIops + costEgress
    uiCost.innerText = cost.toFixed(2)


    // ================================================================
    //  Economic Metrics
    // ================================================================

    var txFeePerKB = getFloat(uiTxFee)                                          //  ADA/kB
    var txFee      = txFeePerKB * txSize / 1000                                 //  ADA/tx
    var price      = getFloat(uiAda)                                            //  USD/ADA
    var totalFees  = txPerSec * txFee * price * T_month                         //  USD/month (network)
    var fraction   = getFloat(uiStake) / 100 * getFloat(uiRetained) / 100       //  SPO share
    var retained   = fraction * totalFees                                        //  USD/month

    uiFees.innerText   = retained.toFixed(2)
    uiProfit.innerText = (retained - cost).toFixed(2)
    uiReturn.innerText = (100 * retained / cost).toFixed(2)

    var txCostUSD = cost / fraction / txPerSec / T_month                         //  USD/tx
    var txCostADA = txCostUSD / price                                            //  ADA/tx
    uiCostTxUsd.innerText = txCostUSD.toFixed(4)
    uiCostTxAda.innerText = txCostADA.toFixed(4)
  }

  function hyperscaleCosts() {
    uiVcpu.value    = "20"
    uiStorage.value = "0.12"
    uiIops.value    = "0.05"
    uiEgress.value  = "0.09"
    calculate()
  }

  function discountCosts() {
    uiVcpu.value    = "20"
    uiStorage.value = "0.10"
    uiIops.value    = "0.00"
    uiEgress.value  = "0.00"
    calculate()
  }

  function initialize() {
    [
      uiASC
    , uiAda
    , uiCompression
    , uiEgress
    , uiFetchMult
    , uiInboundPeers
    , uiIops
    , uiMaxRbBody
    , uiProducers
    , uiCurrentChain
    , uiRelays
    , uiRetained
    , uiSlotRate
    , uiSpike
    , uiStake
    , uiStorage
    , uiThroughput
    , uiTxFee
    , uiTxSize
    , uiVcpu
    , uiVotesPerEB
    , uiVotingWindow
    ].forEach(function(el) { el.addEventListener("input", calculate) })

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
    initialize: initialize
  }

})()
