
'use strict'


import * as d3  from "d3"


const millisecond = 0.001                 //  s/ms
const bit = 1 / 8                         //  b/B
const kilobyte = 1000                     //  B/kB
const gigabyte = 1000 * 1000 * 1000       //  B/GB
const month = 365.24 / 12 * 24 * 60 * 60  //  s/month


function getFloat(ui) {
  return parseFloat(ui.value)
}

function roundTwo(x) {
  return Math.round(100 * x) / 100
}

function sumResources(resources) {
  return {
    throughput   : resources.reduce((sum, resource) => sum + resource.throughput  , 0)
  , disk         : resources.reduce((sum, resource) => sum + resource.disk        , 0)
  , producerVcpu : resources.reduce((sum, resource) => sum + resource.producerVcpu, 0)
  , relayVcpu    : resources.reduce((sum, resource) => sum + resource.relayVcpu   , 0)
  , io           : resources.reduce((sum, resource) => sum + resource.io          , 0)
  }
}


function calculateResources(rate /*  item/s  */, elSize, elIo, elBuild, elVerify, persistent) {

  const slot = getFloat(uiSlotRate)          //  slot/s
  const size = getFloat(elSize)              //  kB/item
  const io = getFloat(elIo)                  //  IO/item
  const build = getFloat(elBuild)            //  vCPU*ms/item
  const verify = getFloat(elVerify)          //  vCPU*ms/item
  const bps = size * rate * slot * kilobyte  //  B/s

  return {
    throughput   : bps                                           //  B/s
  , disk         : persistent ? bps : 0                          //  B/s
  , producerVcpu : Math.max(build, verify) * rate * millisecond  //  vCPU
  , relayVcpu    : verify * rate * millisecond                   //  vCPU
  , io           : io * rate                                     //  IO/s
  }

}

function ibResources() {
  const rate = getFloat(uiIbRate)  //  IB/slot
  return calculateResources(rate, uiIbSize, uiIbIo, uiIbBuild, uiIbVerify, true)
}

function ebResources() {
  const ebRate = getFloat(uiEbRate)      //  EB/pipline
  const pipeline = getFloat(uiPipeline)  //  slot/pipeline
  const rate = ebRate / pipeline         //  EB/slot
  return calculateResources(rate, uiEbSize, uiEbIo, uiEbBuild, uiEbVerify, true)
}

function voteResources() {
  const voteRate = getFloat(uiVoteRate)  //  vote/pipline
  const pipeline = getFloat(uiPipeline)  //  slot/pipeline
  const rate = voteRate / pipeline       //  vote/slot
  return calculateResources(rate, uiVoteSize, uiVoteIo, uiVoteBuild, uiVoteVerify, false)
}

function certResources() {
  const certRate = getFloat(uiCertRate)  //  cert/pipline
  const pipeline = getFloat(uiPipeline)  //  slot/pipeline
  const rate = certRate / pipeline       //  cert/slot
  return calculateResources(rate, uiCertSize, uiCertIo, uiCertBuild, uiCertVerify, false)
}

function rbResources() {
  const rate = getFloat(uiRbRate)  //  RB/slot
  return calculateResources(rate, uiCertSize, uiCertIo, uiCertBuild, uiCertVerify, true)
}

function txResources() {

  const rate = getFloat(uiPraosTx) + getFloat(uiLeiosTx)  //  tx/s
  const size = getFloat(uiTxSize)                         //  kB/tx
  const verify = getFloat(uiTxVerify)                     //  vCPU*ms/tx
  const vcpu = rate * verify * millisecond                //  vCPU
  const mempool = rate * size * kilobyte                  //  B/s

  return {
    throughput   : mempool
  , disk         : 0
  , producerVcpu : vcpu
  , relayVcpu    : vcpu
  , io           : 0
  }

}


export async function calculate() {

  const slot = getFloat(uiSlotRate)  //  slot/s
  const phases = getFloat(uiPhases)  //  phase/pipeline
  const phase = getFloat(uiPhase)    //  slot/phase

  const pipeline = phases * phase    //  slot/pipeline
  uiPipeline.value = pipeline

  const ibRate = getFloat(uiIbRate)        //  IB/slot
  const certRate = getFloat(uiCertRate)    //  cert/pipeline
  const rbRate = getFloat(uiRbRate)        //  RB/slot

  const praosTxRate = getFloat(uiPraosTx)  //  tx/s
  const leiosTxRate = getFloat(uiLeiosTx)  //  tx/s

  const txSize = getFloat(uiTxSize)        //  kB/tx
  const certSize = getFloat(uiCertSize)    //  kB/cert

  uiRbSize.value = (praosTxRate * txSize / rbRate + certRate * certSize) / slot  //  kB/RB
  uiIbSize.value = leiosTxRate * txSize / ibRate / slot                          //  kB/IB

  const resources = sumResources([
    ibResources()
  , ebResources()
  , voteResources()
  , certResources()
  , rbResources()
  , txResources()
  ])

  const spike = getFloat(uiSpike)
  const producers = getFloat(uiProducers)
  const relays = getFloat(uiRelays)
  const nodes = producers + relays

  const vcpu = producers * Math.max(2, Math.ceil(spike * resources.producerVcpu))
             + relays    * Math.max(2, Math.ceil(spike * resources.relayVcpu   ))
  uiTotalVcpu.innerText = vcpu
  const costVcpu = roundTwo(vcpu * getFloat(uiVcpu))
  uiCostVcpu.innerText = costVcpu

  const discount = (1 - getFloat(uiDiscount) / 100) / 12                                            //  1/month
  const perpetual = (1 + discount) / discount                                                       //  1
  const compression = 1 - getFloat(uiCompression) / 100                                             //  1
  const storage = nodes * compression * (getFloat(uiRbLedger) + resources.disk / gigabyte * month)  //  GB/month
  uiTotalStorage.innerText = roundTwo(storage)
  const costStorage = roundTwo(storage * perpetual * getFloat(uiStorage)) 
  uiCostStorage.innerText = costStorage

  const throughput = resources.throughput                     //  B/s
  const downstream = getFloat(uiDownsteam) * throughput       //  B/s
  const upstream = getFloat(uiUpstream) * throughput          //  B/S
  const network = (downstream + upstream) / gigabyte * month  //  GB/month
  uiTotalEgress.innerText = roundTwo(network)
  const costEgress = roundTwo(network * getFloat(uiEgress))
  uiCostEgress.innerText = costEgress

  uiNic.innerText = Math.max(1, Math.round(Math.pow(10, Math.ceil(Math.log(spike * Math.max(upstream, downstream) / gigabyte / bit) / Math.log(10)))))  // Gb/s

  const io = nodes * resources.io  // IO/s
  uiTotalIops.innerText = roundTwo(io)
  const costIops = roundTwo(io * getFloat(uiIops))
  uiCostIops.innerText = costIops

  const cost = costVcpu + costStorage + costIops + costEgress
  uiCost.innerText = cost

  const txRate = praosTxRate + leiosTxRate                                           //  tx/s
  const txFee = getFloat(uiTxFee)                                                    //  ADA/tx
  const price = getFloat(uiAda)                                                      //  USD/ADA
  const totalFees = txRate * txFee * price * month                                   //  USD/month
  const retained = getFloat(uiStake) / 100 * getFloat(uiRetained) / 100 * totalFees  //  USD/month
  uiFees.innerText = roundTwo(retained)
  uiProfit.innerText = roundTwo(retained - cost)
  uiReturn.innerText = roundTwo(100 * retained / cost)
  
}

export async function initialize() {
  [
    uiAda
  , uiCertBuild
  , uiCertIo
  , uiCertRate
  , uiCertSize
  , uiCertVerify
  , uiCompression
  , uiDiscount
  , uiDownsteam
  , uiEbBuild
  , uiEbIo
  , uiEbRate
  , uiEbSize
  , uiEbVerify
  , uiEgress
  , uiIbBuild
  , uiIbIo
  , uiIbRate
//, uiIbSize
  , uiIbVerify
  , uiIops
  , uiLeiosTx
  , uiNic
  , uiPhase
//, uiPhases
//, uiPipeline
  , uiPraosTx
  , uiProducers
  , uiProfit
  , uiRbBuild
  , uiRbLedger
  , uiRbRate
//, uiRbSize
  , uiRbVerify
  , uiRelays
  , uiRetained
  , uiReturn
  , uiSlotRate
  , uiSpike
  , uiStake
  , uiStorage
  , uiTxFee
  , uiTxSize
  , uiTxVerify
  , uiUpstream
//, uiVariant
  , uiVariants
  , uiVcpu
  , uiVoteBuild
  , uiVoteIo
  , uiVoteRate
  , uiVoteSize
  , uiVoteVerify
  ].forEach(el => el.addEventListener("input", calculate))

  calculate()
}
