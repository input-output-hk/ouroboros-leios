
'use strict'

import * as gen from "./gen"

import * as d3  from "d3"


const millisecond = 0.001                 //  s/ms
const bit = 1 / 8                         //  B/b
const kilobyte = 1024                     //  B/kB
const gigabyte = 1024 * 1024 * 1024       //  B/GB
const month = 365.24 / 12 * 24 * 60 * 60  //  s/month


function getFloat(ui) {
  return parseFloat(ui.value)
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


function calculateResources(rate /*  item/slot  */, elSize, elIo, elBuild, elVerify, persistent) {

  const slot = getFloat(uiSlotRate)          //  slot/s
  const size = getFloat(elSize)              //  kB/item
  const io = getFloat(elIo)                  //  IO/item
  const build = getFloat(elBuild)            //  vCPU*ms/item
  const verify = getFloat(elVerify)          //  vCPU*ms/item
  const bps = size * rate * slot * kilobyte  //  B/s

  return {
    throughput   : bps                                                  //  B/s
  , disk         : persistent ? bps : 0                                 //  B/s
  , producerVcpu : Math.max(build, verify) * rate * slot * millisecond  //  vCPU
  , relayVcpu    : verify * rate * slot * millisecond                   //  vCPU
  , io           : io * rate * slot                                     //  IO/s
  }

}

function ibResources() {
  const rate = getFloat(uiIbRate)  //  IB/slot
  return calculateResources(rate, uiIbSize, uiIbIo, uiIbBuild, uiIbVerify, true)
}

function ebResources() {
  const ebRate = getFloat(uiEbRate)      //  EB/pipline
  const pipeline = getFloat(uiPhase)     //  slot/pipeline
  const rate = ebRate / pipeline         //  EB/slot
  return calculateResources(rate, uiEbSize, uiEbIo, uiEbBuild, uiEbVerify, true)
}

function voteResources() {
  const voteRate = getFloat(uiVoteRate)  //  vote/pipline
  const pipeline = getFloat(uiPhase)     //  slot/pipeline
  const rate = voteRate / pipeline       //  vote/slot
  return calculateResources(rate, uiVoteSize, uiVoteIo, uiVoteBuild, uiVoteVerify, false)
}

function certResources() {
  const certRate = getFloat(uiCertRate)  //  cert/pipline
  const pipeline = getFloat(uiPhase)     //  slot/pipeline
  const rate = certRate / pipeline       //  cert/slot
  return calculateResources(rate, uiCertSize, uiCertIo, uiCertBuild, uiCertVerify, false)
}

function rbResources() {
  const rate = getFloat(uiRbRate)  //  RB/slot
  const uiRbIo = uiCertIo
  return calculateResources(rate, uiCertSize, uiRbIo, uiRbBuild, uiRbVerify, true)
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

  // The variable names and units are awkard here: Because of Leios
  // parallelism, the number of slots per pipeline equals the number
  // of phases per pipeline.

  const slot = getFloat(uiSlotRate)   //  slot/s
  const phases = getFloat(uiPhases)   //  phase/pipeline
  const pipeline = getFloat(uiPhase)  //  slot/pipeline

  const ibRate = getFloat(uiIbRate)      //  IB/slot
  const ebRate = getFloat(uiEbRate)      //  EB/pipeline
  const certRate = getFloat(uiCertRate)  //  cert/pipeline
  const rbRate = getFloat(uiRbRate)      //  RB/slot

  const praosTxRate = getFloat(uiPraosTx)  //  tx/s
  const leiosTxRate = getFloat(uiLeiosTx)  //  tx/s

  const txSize = getFloat(uiTxSize)      //  kB/tx
  const ibRefSize = getFloat(uiIbRef)    //  kB/IBref
  const certSize = getFloat(uiCertSize)  //  kB/cert

  uiRbSize.value = ((praosTxRate * txSize / slot + certRate * certSize / pipeline) / rbRate).toFixed(2)       //  kB/RB
  uiIbSize.value = (leiosTxRate == 0 && ibRate == 0 ? 0 : leiosTxRate * txSize / ibRate / slot).toFixed(2)    //  kB/IB
  uiEbSize.value = (leiosTxRate == 0 && ibRate == 0 ? 0 : ibRate * pipeline / ebRate * ibRefSize).toFixed(2)  //  kB/EB

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
  const costVcpu = vcpu * getFloat(uiVcpu)
  uiCostVcpu.innerText = costVcpu.toFixed(2)

  const discount = getFloat(uiDiscount) / 100 / 12                                                  //  1/month
  const perpetual = (1 + discount) / discount                                                       //  1
  const compression = 1 - getFloat(uiCompression) / 100                                             //  1
  const storage = nodes * compression * (getFloat(uiRbLedger) + resources.disk / gigabyte * month)  //  GB/month
  uiTotalStorage.innerText = storage.toFixed(2)
  const costStorage = storage * perpetual * getFloat(uiStorage)
  uiCostStorage.innerText = costStorage.toFixed(2)

  const throughput = resources.throughput                     //  B/s
  const downstream = getFloat(uiDownsteam) * throughput       //  B/s
  const upstream = getFloat(uiUpstream) * throughput          //  B/S
  const network = (downstream + upstream) / gigabyte * month  //  GB/month
  uiTotalEgress.innerText = network.toFixed(2)
  const costEgress = network * getFloat(uiEgress)
  uiCostEgress.innerText = costEgress.toFixed(2)

  uiNic.innerText = Math.max(1, Math.round(Math.pow(10, Math.ceil(Math.log(spike * Math.max(upstream, downstream) / gigabyte / bit) / Math.log(10)))))  // Gb/s

  const io = spike * nodes * resources.io  // IO/s
  uiTotalIops.innerText = io.toFixed(2)
  const costIops = io * getFloat(uiIops)
  uiCostIops.innerText = costIops.toFixed(2)

  const cost = costVcpu + costStorage + costIops + costEgress
  uiCost.innerText = cost.toFixed(2)

  const txRate = praosTxRate + leiosTxRate                               //  tx/s
  const txFee = getFloat(uiTxFee) * getFloat(uiTxSize)                   //  ADA/tx
  const price = getFloat(uiAda)                                          //  USD/ADA
  const totalFees = txRate * txFee * price * month                       //  USD/month
  const fraction = getFloat(uiStake) / 100 * getFloat(uiRetained) / 100  //  %/100
  const retained = fraction * totalFees                                  //  USD/month

  uiFees.innerText = retained.toFixed(2)
  uiProfit.innerText = (retained - cost).toFixed(2)
  uiReturn.innerText = (100 * retained / cost).toFixed(2)

  const txCostUSD = cost / fraction / txRate / month  //  USD/tx
  const txCostADA = txCostUSD / price                 //  ADA/tx
  uiCostTxUsd.innerText = txCostUSD.toFixed(2)
  uiCostTxAda.innerText = txCostADA.toFixed(2)
  
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
//, uiEbSize
  , uiEbVerify
  , uiEgress
  , uiIbBuild
  , uiIbIo
  , uiIbRate
  , uiIbRef
//, uiIbSize
  , uiIbVerify
  , uiIops
  , uiLeiosTx
  , uiPhase
//, uiPhases
  , uiPraosTx
  , uiProducers
  , uiRbBuild
  , uiRbLedger
  , uiRbRate
//, uiRbSize
  , uiRbVerify
  , uiRelays
  , uiRetained
  , uiSlotRate
  , uiSpike
  , uiStake
  , uiStorage
  , uiTxFee
  , uiTxSize
  , uiTxVerify
  , uiUpstream
//, uiVariant
  , uiVcpu
  , uiVoteBuild
  , uiVoteIo
  , uiVoteRate
  , uiVoteSize
  , uiVoteVerify
  ].forEach(el => el.addEventListener("input", calculate))

  calculate()

  console.log(gen.Test.x)
}
