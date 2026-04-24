
'use strict'


// Constants
const GiB = 1024 * 1024 * 1024            //  B/GiB
const T_month = 365.24 / 12 * 24 * 3600   //  s/month  ≈ 2,628,000


function getFloat(el) {
  return parseFloat(el.value)
}


export async function calculate() {

  // === Protocol Parameters ===

  const f = getFloat(uiASC)                          //  active slot coefficient
  const slotRate = getFloat(uiSlotRate)               //  slot/s
  const ebRate = f * slotRate                         //  EB/s  =  RB/s
  const votingWindow = getFloat(uiVotingWindow)       //  slots
  const votesPerEB = getFloat(uiVotesPerEB)           //  votes/EB
  const pCert = Math.pow(1 - f, votingWindow)         //  P(EB certified)
  const rCert = ebRate * pCert                        //  certified EB/s

  uiPcert.innerText = (pCert * 100).toFixed(1)

  // === Throughput ===

  const txkBps = getFloat(uiThroughput)               //  confirmed TxkB/s
  const txSize = getFloat(uiTxSize)                   //  B/tx
  const txPerSec = txkBps * 1000 / txSize             //  tx/s  (1 kB = 1000 B)
  uiTxPerSec.innerText = Math.round(txPerSec)

  // === Component Sizes (bytes) ===

  const voteSize = getFloat(uiVoteSize)               //  B/vote
  const ebHeaderSize = getFloat(uiEbHeaderSize)       //  B/EB header
  const txRefSize = getFloat(uiTxRefSize)             //  B/tx hash reference
  const certSize = getFloat(uiCertSize)               //  B/certificate
  const rbHeaderSize = getFloat(uiRbHeaderSize)       //  B/RB header

  // === Validation Times (ms) ===

  const txApplyMs = getFloat(uiTxApply)               //  ms/tx
  const ebHeaderValMs = getFloat(uiEbHeaderVal)       //  ms/EB
  const voteValMs = getFloat(uiVoteVal)               //  ms/vote
  const certValMs = getFloat(uiCertVal)               //  ms/cert

  // Reapply constants (from CIP-164 config: eb-body-validation-cpu-time-ms-*)
  const reapplyConstMs = 0.3539                       //  ms/EB
  const reapplyPerByteMs = 0.00002151                 //  ms/B

  // === Network Topology ===

  const inboundPeers = getFloat(uiInboundPeers)      //  downstream peers per relay
  const fetchMult = getFloat(uiFetchMult)             //  fetch multiplicity M
  const voteRedundancy = getFloat(uiVoteRedundancy)   //  spanning-tree redundancy
  const outboundPeers = 25                            //  upstream peers (fixed)
  const bodyFetchPeers = inboundPeers * fetchMult / outboundPeers


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
  //

  const cpuApply    = txPerSec * txApplyMs
  const cpuReapply  = ebRate * reapplyConstMs + reapplyPerByteMs * txkBps * 1000
  const cpuEbHeader = ebRate * ebHeaderValMs
  const cpuVote     = votesPerEB * ebRate * voteValMs
  const cpuCert     = ebRate * certValMs
  const cpuTotal    = cpuApply + cpuReapply + cpuEbHeader + cpuVote + cpuCert

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
  //

  const storageTx     = txkBps * 1000 * T_month / GiB                                //  tx closure data
  const storageEbBody = txPerSec * txRefSize * T_month / GiB                          //  EB body (tx hashes)
  const storageEbHdr  = rCert * ebHeaderSize * T_month / GiB                          //  certified EB headers
  const storageRb     = ebRate * (rbHeaderSize + certSize) * T_month / GiB             //  RB headers + certs (simplified: every RB carries a cert)
  const storageMonthly = storageTx + storageEbBody + storageEbHdr + storageRb


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
  //

  const egressTx      = txkBps * 1000 * 1 * T_month / GiB
  const egressVotes   = votesPerEB * voteSize * ebRate * voteRedundancy * T_month / GiB
  const egressEbBody  = txPerSec * txRefSize / pCert * bodyFetchPeers * T_month / GiB
  const egressRbHdr   = ebRate * rbHeaderSize * inboundPeers * T_month / GiB
  const egressRbCert  = rCert * certSize * bodyFetchPeers * T_month / GiB
  const egressMonthly = egressTx + egressVotes + egressEbBody + egressRbHdr + egressRbCert


  // ================================================================
  //  IOPS  (IO/s per node — with UTxO-HD)
  // ================================================================
  //
  //  UTxO state updates dominate (~88% of total).
  //

  const iopsTxData  = txkBps * 1000 / 4096 * 1.1                                //  tx data write + read-back
  const iopsUtxo    = txPerSec * 3                                               //  UTxO-HD inserts/deletes
  const ebBodyBytes = txPerSec / ebRate * txRefSize                              //  bytes per EB body
  const iopsEbBody  = ebRate * Math.ceil(ebBodyBytes / 4096) * 1.2               //  EB body writes
  const iopsRb      = ebRate * 2 * 1.2                                           //  RB writes/reads
  const iopsEbHdr   = rCert * 1.2                                                //  certified EB header writes
  const iopsTotal   = iopsTxData + iopsUtxo + iopsEbBody + iopsRb + iopsEbHdr


  // ================================================================
  //  Resource & Cost Aggregation  (per SPO)
  // ================================================================

  const spike     = getFloat(uiSpike)
  const producers = getFloat(uiProducers)
  const relays    = getFloat(uiRelays)
  const nodes     = producers + relays

  //  vCPU  — minimum 2 cores per node, spike-adjusted
  const cpuCoresNeeded = cpuTotal / 1000                                         //  steady-state cores
  const vcpuPerNode = Math.max(2, Math.ceil(spike * cpuCoresNeeded))
  const vcpu = nodes * vcpuPerNode
  uiTotalVcpu.innerText = vcpu
  const costVcpu = vcpu * getFloat(uiVcpu)
  uiCostVcpu.innerText = costVcpu.toFixed(2)

  //  Storage  — ledger + monthly new data, with optional perpetual amortization
  uiAmortized.style.textDecoration = uiAmortize.checked ? "none" : "line-through"
  const discount   = getFloat(uiDiscount) / 100 / 12                            //  1/month
  const perpetual  = uiAmortize.checked ? (1 + discount) / discount : 1          //  amortization factor
  const compression = 1 - getFloat(uiCompression) / 100                          //  effective ratio
  const ledger     = getFloat(uiRbLedger)                                        //  GB (current ledger)
  const storage    = nodes * compression * (ledger + storageMonthly)              //  GiB total
  uiTotalStorage.innerText = storage.toFixed(2)
  const costStorage = storage * perpetual * getFloat(uiStorage)
  uiCostStorage.innerText = costStorage.toFixed(2)

  //  Network egress  — relay egress × number of relays
  const egressSPO = relays * egressMonthly                                       //  GiB/month
  uiTotalEgress.innerText = egressSPO.toFixed(2)
  const costEgress = egressSPO * getFloat(uiEgress)
  uiCostEgress.innerText = costEgress.toFixed(2)

  //  NIC  — per-relay peak, rounded to nearest power of 10
  const perRelayBps = egressMonthly * GiB / T_month                              //  B/s steady state
  const peakGbps = spike * perRelayBps * 8 / (1000 * 1000 * 1000)               //  Gb/s peak
  uiNic.innerText = Math.max(1, Math.round(Math.pow(10, Math.ceil(Math.log10(Math.max(0.01, peakGbps))))))

  //  IOPS
  const io = spike * nodes * iopsTotal
  uiTotalIops.innerText = io.toFixed(2)
  const costIops = io * getFloat(uiIops)
  uiCostIops.innerText = costIops.toFixed(2)

  //  Total
  const cost = costVcpu + costStorage + costIops + costEgress
  uiCost.innerText = cost.toFixed(2)


  // ================================================================
  //  Economic Metrics
  // ================================================================

  const txFeePerKB = getFloat(uiTxFee)                                          //  ADA/kB
  const txFee      = txFeePerKB * txSize / 1000                                 //  ADA/tx
  const price      = getFloat(uiAda)                                            //  USD/ADA
  const totalFees  = txPerSec * txFee * price * T_month                         //  USD/month (network)
  const fraction   = getFloat(uiStake) / 100 * getFloat(uiRetained) / 100       //  SPO share
  const retained   = fraction * totalFees                                        //  USD/month

  uiFees.innerText   = retained.toFixed(2)
  uiProfit.innerText = (retained - cost).toFixed(2)
  uiReturn.innerText = (100 * retained / cost).toFixed(2)

  const txCostUSD = cost / fraction / txPerSec / T_month                         //  USD/tx
  const txCostADA = txCostUSD / price                                            //  ADA/tx
  uiCostTxUsd.innerText = txCostUSD.toFixed(4)
  uiCostTxAda.innerText = txCostADA.toFixed(4)

}


export async function hyperscaleCosts() {
  uiVcpu.value    = "20"
  uiStorage.value = "0.12"
  uiIops.value    = "0.05"
  uiEgress.value  = "0.09"
  calculate()
}

export async function discountCosts() {
  uiVcpu.value    = "20"
  uiStorage.value = "0.10"
  uiIops.value    = "0.00"
  uiEgress.value  = "0.00"
  calculate()
}


export async function initialize() {
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
  ].forEach(el => el.addEventListener("input", calculate))

  calculate()
}
