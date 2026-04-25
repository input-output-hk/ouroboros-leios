// Linear Leios (CIP-164) cost estimator
// See docs/cost-estimate/ for methodology and cross-checks.

var Controller = (function() {
  'use strict'

  var GiB = 1024 * 1024 * 1024            //  B/GiB
  var T_month = 365.24 / 12 * 24 * 3600   //  s/month  ≈ 2,628,000

  function getFloat(el) {
    return parseFloat(el.value)
  }

  function calculate() {

    // === Protocol Parameters ===

    var f = getFloat(uiASC)                          //  active slot coefficient
    var slotRate = getFloat(uiSlotRate)               //  slot/s
    var ebRate = f * slotRate                         //  EB/s  =  RB/s
    var votingWindow = getFloat(uiVotingWindow)       //  slots
    var votesPerEB = getFloat(uiVotesPerEB)           //  votes/EB
    var pCert = Math.pow(1 - f, votingWindow)         //  P(EB certified)
    var rCert = ebRate * pCert                        //  certified EB/s

    uiPcert.innerText = (pCert * 100).toFixed(1)

    // === Throughput ===

    var txkBps = getFloat(uiThroughput)               //  confirmed TxkB/s
    var txSize = getFloat(uiTxSize)                   //  B/tx
    var txPerSec = txkBps * 1000 / txSize             //  tx/s  (1 kB = 1000 B)
    uiTxPerSec.innerText = Math.round(txPerSec)

    // === Component Sizes (bytes) ===

    var voteSize = getFloat(uiVoteSize)               //  B/vote
    var ebHeaderSize = getFloat(uiEbHeaderSize)       //  B/EB header
    var txRefSize = getFloat(uiTxRefSize)             //  B/tx hash reference
    var certSize = getFloat(uiCertSize)               //  B/certificate
    var rbHeaderSize = getFloat(uiRbHeaderSize)       //  B/RB header

    // === Validation Times (ms) ===

    var txApplyMs = getFloat(uiTxApply)               //  ms/tx
    var ebHeaderValMs = getFloat(uiEbHeaderVal)       //  ms/EB
    var voteValMs = getFloat(uiVoteVal)               //  ms/vote
    var certValMs = getFloat(uiCertVal)               //  ms/cert

    // Reapply constants (from CIP-164 config: eb-body-validation-cpu-time-ms-*)
    var reapplyConstMs = 0.3539                       //  ms/EB
    var reapplyPerByteMs = 0.00002151                 //  ms/B

    // === Network Topology ===

    var inboundPeers = getFloat(uiInboundPeers)      //  downstream peers per relay
    var fetchMult = getFloat(uiFetchMult)             //  fetch multiplicity M
    var voteRedundancy = getFloat(uiVoteRedundancy)   //  spanning-tree redundancy
    var outboundPeers = 25                            //  upstream peers (fixed)
    var bodyFetchPeers = inboundPeers * fetchMult / outboundPeers


    // ================================================================
    //  CPU  (ms/s per node)
    // ================================================================
    //
    //  Five components from the CIP-164 cost analysis:
    //  1. Tx Apply       — full validation at mempool ingestion
    //  2. Tx Reapply     — ledger application when EB is certified
    //  3. EB header      — EB/RB header validation
    //  4. Vote           — individual BLS vote verification
    //  5. Certificate    — certificate validation

    var cpuApply    = txPerSec * txApplyMs
    var cpuReapply  = ebRate * reapplyConstMs + reapplyPerByteMs * txkBps * 1000
    var cpuEbHeader = ebRate * ebHeaderValMs
    var cpuVote     = votesPerEB * ebRate * voteValMs
    var cpuCert     = ebRate * certValMs
    var cpuTotal    = cpuApply + cpuReapply + cpuEbHeader + cpuVote + cpuCert

    uiCpuApply.innerText    = cpuApply.toFixed(2)
    uiCpuReapply.innerText  = cpuReapply.toFixed(2)
    uiCpuEbHeader.innerText = cpuEbHeader.toFixed(3)
    uiCpuVote.innerText     = cpuVote.toFixed(1)
    uiCpuCert.innerText     = cpuCert.toFixed(2)
    uiCpuTotal.innerText    = cpuTotal.toFixed(1)
    uiCpuPercent.innerText  = (cpuTotal / 10).toFixed(1)


    // ================================================================
    //  Storage  (GiB/month per node — new data only)
    // ================================================================
    //
    //  Only confirmed data is persisted.  P(cert) cancels for EB body
    //  storage (certified EBs are larger).  Votes are ephemeral.

    var storageTx     = txkBps * 1000 * T_month / GiB                                //  tx closure data
    var storageEbBody = txPerSec * txRefSize * T_month / GiB                          //  EB body (tx hashes)
    var storageEbHdr  = rCert * ebHeaderSize * T_month / GiB                          //  certified EB headers
    var storageRb     = ebRate * (rbHeaderSize + certSize) * T_month / GiB            //  RB headers + certs
    var storageMonthly = storageTx + storageEbBody + storageEbHdr + storageRb


    // ================================================================
    //  Egress  (GiB/month per relay node)
    // ================================================================
    //
    //  Five traffic components with different peer models:
    //  1. Tx mempool diffusion  — 1 effective peer (fetch-from-one)
    //  2. Vote gossip           — spanning-tree × redundancy
    //  3. EB bodies (tx refs)   — bodyFetchPeers, ×1/P(cert) overcounting
    //  4. RB/EB headers         — pushed to all inbound peers
    //  5. RB cert bodies        — certified RBs only, bodyFetchPeers

    var egressTx      = txkBps * 1000 * 1 * T_month / GiB
    var egressVotes   = votesPerEB * voteSize * ebRate * voteRedundancy * T_month / GiB
    var egressEbBody  = txPerSec * txRefSize / pCert * bodyFetchPeers * T_month / GiB
    var egressRbHdr   = ebRate * rbHeaderSize * inboundPeers * T_month / GiB
    var egressRbCert  = rCert * certSize * bodyFetchPeers * T_month / GiB
    var egressMonthly = egressTx + egressVotes + egressEbBody + egressRbHdr + egressRbCert


    // ================================================================
    //  IOPS  (IO/s per node — with UTxO-HD)
    // ================================================================
    //
    //  UTxO state updates dominate (~88% of total).

    var iopsTxData  = txkBps * 1000 / 4096 * 1.1                                //  tx data write + read-back
    var iopsUtxo    = txPerSec * 3                                               //  UTxO-HD inserts/deletes
    var ebBodyBytes = txPerSec / ebRate * txRefSize                              //  bytes per EB body
    var iopsEbBody  = ebRate * Math.ceil(ebBodyBytes / 4096) * 1.2               //  EB body writes
    var iopsRb      = ebRate * 2 * 1.2                                           //  RB writes/reads
    var iopsEbHdr   = rCert * 1.2                                                //  certified EB header writes
    var iopsTotal   = iopsTxData + iopsUtxo + iopsEbBody + iopsRb + iopsEbHdr


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

    //  Storage  — ledger + monthly new data, with optional perpetual amortization
    uiAmortized.style.textDecoration = uiAmortize.checked ? "none" : "line-through"
    var discount   = getFloat(uiDiscount) / 100 / 12                            //  1/month
    var perpetual  = uiAmortize.checked ? (1 + discount) / discount : 1          //  amortization factor
    var compression = 1 - getFloat(uiCompression) / 100                          //  effective ratio
    var ledger     = getFloat(uiRbLedger)                                        //  GB (current ledger)
    var storage    = nodes * compression * (ledger + storageMonthly)              //  GiB total
    uiTotalStorage.innerText = storage.toFixed(2)
    var costStorage = storage * perpetual * getFloat(uiStorage)
    uiCostStorage.innerText = costStorage.toFixed(2)

    //  Network egress  — relay egress × number of relays
    var egressSPO = relays * egressMonthly                                       //  GiB/month
    uiTotalEgress.innerText = egressSPO.toFixed(2)
    var costEgress = egressSPO * getFloat(uiEgress)
    uiCostEgress.innerText = costEgress.toFixed(2)

    //  NIC  — per-relay peak, rounded to nearest power of 10
    var perRelayBps = egressMonthly * GiB / T_month                              //  B/s steady state
    var peakGbps = spike * perRelayBps * 8 / (1000 * 1000 * 1000)               //  Gb/s peak
    uiNic.innerText = Math.max(1, Math.round(Math.pow(10, Math.ceil(Math.log10(Math.max(0.01, peakGbps))))))

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
    , uiAmortize
    , uiCertSize
    , uiCertVal
    , uiCompression
    , uiDiscount
    , uiEbHeaderSize
    , uiEbHeaderVal
    , uiEgress
    , uiFetchMult
    , uiInboundPeers
    , uiIops
    , uiProducers
    , uiRbHeaderSize
    , uiRbLedger
    , uiRelays
    , uiRetained
    , uiSlotRate
    , uiSpike
    , uiStake
    , uiStorage
    , uiThroughput
    , uiTxApply
    , uiTxFee
    , uiTxRefSize
    , uiTxSize
    , uiVcpu
    , uiVoteRedundancy
    , uiVoteSize
    , uiVoteVal
    , uiVotesPerEB
    , uiVotingWindow
    ].forEach(function(el) { el.addEventListener("input", calculate) })

    calculate()
  }

  return {
    calculate: calculate,
    hyperscaleCosts: hyperscaleCosts,
    discountCosts: discountCosts,
    initialize: initialize
  }

})()
