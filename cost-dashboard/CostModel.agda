module CostModel where


import Agda.Builtin.Float as Flt
import Data.Float as Flt
import Data.Integer as Int

open import Agda.Builtin.Bool using (true ; false)
open import Agda.Builtin.Maybe using (nothing ; just)
open import Data.Float using (Float)
open import Data.Integer using (ℤ ; 0ℤ ; 1ℤ )


record Units : Set where
  field seconds   : ℤ
        bytes     : ℤ
        vcpus     : ℤ
        ios       : ℤ
        slots     : ℤ
        pipelines : ℤ
        ibs       : ℤ
        ebs       : ℤ
        votes     : ℤ
        certs     : ℤ
        rbs       : ℤ
        txs       : ℤ
        usds      : ℤ
        adas      : ℤ

private

  on : {a b c : Set} → (b → b → c) → (a → b) → a → a → c
  on f g x y = f (g x) (g y)
  
  apply : (ℤ → ℤ → ℤ) → Units → Units → Units
  apply f u v = let open Units in
           record {
             seconds   = on f seconds   u v
           ; bytes     = on f bytes     u v
           ; vcpus     = on f vcpus     u v
           ; ios       = on f ios       u v
           ; slots     = on f slots     u v
           ; pipelines = on f pipelines u v 
           ; ibs       = on f ibs       u v
           ; ebs       = on f ebs       u v
           ; votes     = on f votes     u v
           ; certs     = on f certs     u v
           ; rbs       = on f rbs       u v
           ; txs       = on f txs       u v
           ; usds      = on f usds      u v
           ; adas      = on f adas      u v
           }
  
_*ᵤ_ : Units → Units → Units
_*ᵤ_ = apply Int._+_
infixl 4 _*ᵤ_

_/ᵤ_ : Units → Units → Units
_/ᵤ_ = apply Int._-_
infixl 4 _/ᵤ_


record Quantity (u : Units) : Set where
  field value : Float

private

  -- For convenience we require `0/0 ≡ 0`.
  safeDivide : Float → Float → Float
  safeDivide x y = save (x Flt.÷ y)
    where save : Float → Float
          save z with Flt.primFloatIsNaN z
          ... | true  = 0.0
          ... | false = z

ceil : {u : Units} → Quantity u → Quantity u
ceil x with Flt.primFloatCeiling (Quantity.value x)
... | just y  = record { value = Flt.primIntToFloat y }
... | nothing = x

max : {u : Units} → Quantity u → Quantity u → Quantity u
max x y with Flt.primFloatLess (Quantity.value x) (Quantity.value y)
... | true  = y
... | false = x

_‣_ : (u : Units) → Quantity u → Quantity u
_ ‣ x = x
infixl 1 _‣_

quantity : {u : Units} → Float → Quantity u
quantity x = record { value = x }

_∷ᵤ_ : Float → (u : Units) → Quantity u
x ∷ᵤ _ = quantity x
infixl 1 _∷ᵤ_

zero : {u : Units} → Quantity u
zero = quantity 0.0

one : {u : Units} → Quantity u
one = quantity 1.0

_×ᵤ_ : {u : Units} → Float → Quantity u → Quantity u
a ×ᵤ x = record { value = a Flt.* Quantity.value x }
infixl 7 _×ᵤ_

_+_ : {u : Units} → Quantity u → Quantity u → Quantity u
x + y = record { value = on Flt._+_ Quantity.value x y }
infixl 4 _+_

_-_ : {u : Units} → Quantity u → Quantity u → Quantity u
x - y = record { value = on Flt._-_ Quantity.value x y }
infixl 4 _-_

_*_ : {u v : Units} → Quantity u → Quantity v → Quantity (u *ᵤ v)
x * y = let open Quantity in record { value = value x Flt.* value y }
infixl 6 _*_

_/_ : {u v : Units} → Quantity u → Quantity v → Quantity (u /ᵤ v)
x / y = let open Quantity in record { value = safeDivide (value x) (value y) }
infixl 6 _/_

  
unitless : Units
unitless = record
           {
             seconds   = 0ℤ
           ; bytes     = 0ℤ
           ; vcpus     = 0ℤ
           ; ios       = 0ℤ
           ; slots     = 0ℤ
           ; pipelines = 0ℤ
           ; ibs       = 0ℤ
           ; ebs       = 0ℤ
           ; votes     = 0ℤ
           ; certs     = 0ℤ
           ; rbs       = 0ℤ
           ; txs       = 0ℤ
           ; usds      = 0ℤ
           ; adas      = 0ℤ
           }

val : Quantity unitless → Float
val = Quantity.value

1hundred : Quantity unitless
1hundred = quantity 100.0

s : Units
s = record unitless { seconds = 1ℤ }

1s : Quantity s
1s = one

1ms : Quantity s
1ms = quantity 0.001

1month : Quantity s
1month = quantity (365.24 Flt.÷ 12.0 Flt.* 24.0 Flt.* 60.0 Flt.* 60.0)

B : Units
B = record unitless { bytes = 1ℤ }

1Gb : Quantity B
1Gb = quantity (1024.0 Flt.* 1024.0 Flt.* 1024.0 Flt.÷ 8.0)

1kB : Quantity B
1kB = quantity 1024.0

1GB : Quantity B
1GB = quantity (1024.0 Flt.* 1024.0 Flt.* 1024.0)

vCPU : Units
vCPU = record unitless { vcpus = 1ℤ }

1vCPU : Quantity vCPU
1vCPU = one

IO : Units
IO = record unitless { ios = 1ℤ }

1IO : Quantity IO
1IO = one

slot : Units
slot = record unitless { slots = 1ℤ }

1slot : Quantity slot
1slot = one

pipeline : Units
pipeline = record unitless { pipelines = 1ℤ }

1pipeline : Quantity pipeline
1pipeline = one

IB : Units
IB = record unitless { ibs = 1ℤ }

1IB : Quantity IB
1IB = one

EB : Units
EB = record unitless { ebs = 1ℤ }

1EB : Quantity EB
1EB = one

vote : Units
vote = record unitless { votes = 1ℤ }

1vote : Quantity vote
1vote = one

cert : Units
cert = record unitless { certs = 1ℤ }

1cert : Quantity cert
1cert = one

RB : Units
RB = record unitless { rbs = 1ℤ }

1RB : Quantity RB
1RB = one

tx : Units
tx = record unitless { txs = 1ℤ }

1tx : Quantity tx
1tx = one

USD : Units
USD = record unitless { usds = 1ℤ }

1USD : Quantity USD
1USD = one

ADA : Units
ADA = record unitless { adas = 1ℤ }

1ADA : Quantity ADA
1ADA = one


record Resources : Set where
  field throughput   : Quantity (B /ᵤ s)
        disk         : Quantity (B /ᵤ s)
        producerVcpu : Quantity vCPU
        relayVcpu    : Quantity vCPU
        io           : Quantity (IO /ᵤ s)


_+ᵣ_ : Resources → Resources → Resources
x +ᵣ y = let open Resources
        in record
           {
             throughput   = on _+_ throughput   x y
           ; disk         = on _+_ disk         x y
           ; producerVcpu = on _+_ producerVcpu x y
           ; relayVcpu    = on _+_ relayVcpu    x y
           ; io           = on _+_ io           x y
           }
infixl 3 _+ᵣ_


private

  ibResources : Quantity (slot /ᵤ s)
              → Quantity (IB /ᵤ slot)
              → Quantity (B /ᵤ IB)
              → Quantity (IO /ᵤ IB)
              → Quantity (vCPU *ᵤ s /ᵤ IB)
              → Quantity (vCPU *ᵤ s /ᵤ IB)
              → Resources
  ibResources slotLength ibRate size io build verify =
    let rate = ibRate * slotLength
        bps = size * rate
    in record
       {
         throughput   = bps
       ; disk         = bps
       ; producerVcpu = build * rate
       ; relayVcpu    = verify * rate
       ; io           = io * rate
       }
  
  ebResources : Quantity (slot /ᵤ s)
              → Quantity (slot /ᵤ pipeline)
              → Quantity (EB /ᵤ pipeline)
              → Quantity (B /ᵤ EB)
              → Quantity (IO /ᵤ EB)
              → Quantity (vCPU *ᵤ s /ᵤ EB)
              → Quantity (vCPU *ᵤ s /ᵤ EB)
              → Resources
  ebResources slotLength pipelineLength ebRate size io build verify =
    let rate = ebRate / pipelineLength * slotLength
        bps = size * rate
    in record
       {
         throughput   = bps
       ; disk         = bps
       ; producerVcpu = build * rate
       ; relayVcpu    = verify * rate
       ; io           = io * rate
       }
  
  voteResources : Quantity (slot /ᵤ s)
                → Quantity (slot /ᵤ pipeline)
                → Quantity (vote /ᵤ pipeline)
                → Quantity (B /ᵤ vote)
                → Quantity (IO /ᵤ vote)
                → Quantity (vCPU *ᵤ s /ᵤ vote)
                → Quantity (vCPU *ᵤ s /ᵤ vote)
                → Resources
  voteResources slotLength pipelineLength voteRate size io build verify =
    let rate = voteRate / pipelineLength * slotLength
        bps = size * rate
    in record
       {
         throughput   = bps
       ; disk         = zero
       ; producerVcpu = build * rate
       ; relayVcpu    = verify * rate
       ; io           = io * rate
       }
  
  certResources : Quantity (slot /ᵤ s)
                → Quantity (slot /ᵤ pipeline)
                → Quantity (cert /ᵤ pipeline)
                → Quantity (B /ᵤ cert)
                → Quantity (IO /ᵤ cert)
                → Quantity (vCPU *ᵤ s /ᵤ cert)
                → Quantity (vCPU *ᵤ s /ᵤ cert)
                → Resources
  certResources slotLength pipelineLength certRate size io build verify =
    let rate = certRate / pipelineLength * slotLength
        bps = size * rate
    in record
       {
         throughput   = bps
       ; disk         = zero
       ; producerVcpu = build * rate
       ; relayVcpu    = verify * rate
       ; io           = io * rate
       }
  
  rbResources : Quantity (slot /ᵤ s)
              → Quantity (RB /ᵤ slot)
              → Quantity (B /ᵤ RB)
              → Quantity (IO /ᵤ RB)
              → Quantity (vCPU *ᵤ s /ᵤ RB)
              → Quantity (vCPU *ᵤ s /ᵤ RB)
              → Resources
  rbResources slotLength rbRate size io build verify =
    let rate = rbRate * slotLength
        bps = size * rate
    in record
       {
         throughput   = bps
       ; disk         = bps
       ; producerVcpu = build * rate
       ; relayVcpu    = verify * rate
       ; io           = io * rate
       }
  
  txResources : Quantity (tx /ᵤ s)
              → Quantity (B /ᵤ tx)
              → Quantity (vCPU *ᵤ s /ᵤ tx)
              → Resources
  txResources rate size verify =
    let vcpu = rate * verify
        mempool = rate * size
    in record {
         throughput   = mempool
       ; disk         = zero
       ; producerVcpu = vcpu
       ; relayVcpu    = vcpu
       ; io           = zero
       }


record Scenario : Set where
  field
        slots_per_s             : Float
        phase_per_pipeline      : Float
        slot_per_pipeline       : Float
        
        praos_tx_per_s          : Float
        leios_tx_per_s          : Float
        kb_per_tx               : Float
        verify_vcpu_ms_per_tx   : Float
        
        ib_per_slot             : Float
        io_per_ib               : Float
        build_vcpu_ms_per_ib    : Float
        verify_vcpu_ms_per_ib   : Float
        
        eb_per_pipeline         : Float
        io_per_eb               : Float
        build_vcpu_ms_per_eb    : Float
        verify_vcpu_ms_per_eb   : Float
        
        vote_per_pipeline       : Float
        kb_per_vote             : Float
        io_per_vote             : Float
        build_vcpu_ms_per_vote  : Float
        verify_vcpu_ms_per_vote : Float

        cert_per_pipeline       : Float
        kb_per_cert             : Float
        io_per_cert             : Float
        build_vcpu_ms_per_cert  : Float
        verify_vcpu_ms_per_cert : Float
        
        rb_per_slot             : Float
        kb_per_ibref            : Float
        io_per_rb               : Float
        build_vcpu_ms_per_rb    : Float
        verify_vcpu_ms_per_rb   : Float
        ledger_gb               : Float

        egress_downstream       : Float
        egress_upstream         : Float
        spike                   : Float
        producers               : Float
        relays                  : Float
        stake_percent           : Float
        retained_percent        : Float

        usd_per_ada             : Float
        ada_per_kb              : Float
        
        discount_annual_percent : Float
        compression_percent     : Float

        usd_per_vcpu_month      : Float
        usd_per_gb_month        : Float
        usd_per_iops_month      : Float
        usd_per_gb              : Float


record Result : Set where
  field
        vcpu_per_month         : Float
        disk_gb_per_month      : Float
        iops_per_month         : Float
        egress_gb_per_month    : Float
        nic_gb_s_per_month     : Float

        cpu_usd_per_month      : Float
        disk_usd_per_month     : Float
        iops_usd_per_month     : Float
        egress_usd_per_month   : Float
        total_usd_per_month    : Float

        usd_tx                 : Float
        ada_tx                 : Float

        retained_usd_per_month : Float
        profit_usd_per_month   : Float
        return_percent         : Float

units : (u : Units) → Quantity u → Quantity u
units _ x = x

calculate : Scenario → Result
calculate scenario =
  let open Scenario scenario

      slotLength = slots_per_s ∷ᵤ slot /ᵤ s
      pipelineLength = slot_per_pipeline ∷ᵤ slot /ᵤ pipeline

      txRatePraos = praos_tx_per_s ∷ᵤ tx /ᵤ s
      txRateLeios = leios_tx_per_s ∷ᵤ tx /ᵤ s
      txRate = txRatePraos + txRateLeios
      txSize = kb_per_tx ×ᵤ 1kB / 1tx
      txVerify = verify_vcpu_ms_per_tx ×ᵤ 1vCPU * 1ms / 1tx
      txResult = txResources txRate txSize txVerify

      ibRate = ib_per_slot ∷ᵤ IB /ᵤ slot
      ibSize = txRateLeios * txSize / ibRate / slotLength
      ibIo = io_per_ib ∷ᵤ IO /ᵤ IB
      ibBuild = build_vcpu_ms_per_ib ×ᵤ 1vCPU * 1ms / 1IB
      ibVerify = verify_vcpu_ms_per_ib ×ᵤ 1vCPU * 1ms / 1IB
      ibResult = ibResources slotLength ibRate ibSize ibIo ibBuild ibVerify

      ebRate = eb_per_pipeline ∷ᵤ EB /ᵤ pipeline
      ibRefSize = kb_per_ibref ×ᵤ 1kB / 1IB
      ebSize = ibRate * pipelineLength / ebRate * ibRefSize
      ebIo = io_per_eb ∷ᵤ IO /ᵤ EB
      ebBuild = build_vcpu_ms_per_eb ×ᵤ 1vCPU * 1ms / 1EB
      ebVerify = verify_vcpu_ms_per_eb ×ᵤ 1vCPU * 1ms / 1EB
      ebResult = ebResources slotLength pipelineLength ebRate ebSize ebIo ebBuild ebVerify

      voteRate = vote_per_pipeline ∷ᵤ vote /ᵤ pipeline
      voteSize = kb_per_vote ×ᵤ 1kB / 1vote
      voteIo = io_per_vote ∷ᵤ IO /ᵤ vote
      voteBuild = build_vcpu_ms_per_vote ×ᵤ 1vCPU * 1ms / 1vote
      voteVerify = verify_vcpu_ms_per_vote ×ᵤ 1vCPU * 1ms / 1vote
      voteResult = voteResources slotLength pipelineLength voteRate voteSize voteIo voteBuild voteVerify

      certRate = cert_per_pipeline ∷ᵤ cert /ᵤ pipeline
      certSize = kb_per_cert ×ᵤ 1kB / 1cert
      certIo = io_per_cert ∷ᵤ IO /ᵤ cert
      certBuild = build_vcpu_ms_per_cert ×ᵤ 1vCPU * 1ms / 1cert
      certVerify = verify_vcpu_ms_per_cert ×ᵤ 1vCPU * 1ms / 1cert
      certResult = certResources slotLength pipelineLength certRate certSize certIo certBuild certVerify

      rbRate = rb_per_slot ∷ᵤ RB /ᵤ slot
      rbSize = (txRatePraos * txSize / slotLength + certRate * certSize / pipelineLength) / rbRate
      rbIo = io_per_rb ∷ᵤ IO /ᵤ RB
      rbBuild = build_vcpu_ms_per_rb ×ᵤ 1vCPU * 1ms / 1RB
      rbVerify = verify_vcpu_ms_per_rb ×ᵤ 1vCPU * 1ms / 1RB
      rbResult = rbResources slotLength rbRate rbSize rbIo rbBuild rbVerify

      open Resources (txResult +ᵣ rbResult +ᵣ ibResult +ᵣ ebResult +ᵣ voteResult +ᵣ certResult)

      nodes = producers Flt.+ relays ∷ᵤ unitless

      minVcpu = 2.0 ∷ᵤ vCPU
      vcpuMonthly = vCPU ‣ producers ×ᵤ max minVcpu (ceil (spike ×ᵤ producerVcpu))
                         + relays    ×ᵤ max minVcpu (ceil (spike ×ᵤ relayVcpu   ))
      vcpuUnitCost = usd_per_vcpu_month ∷ᵤ USD /ᵤ vCPU
      vcpuTotalCost = vcpuMonthly * vcpuUnitCost

      compression = one - (compression_percent ∷ᵤ unitless) / 1hundred
      ledger = ledger_gb ×ᵤ 1GB
      diskMonthly = B ‣ nodes * compression * (ledger + disk * 1month)
      discount = (discount_annual_percent Flt.÷ 12.0 ∷ᵤ unitless) / 1hundred
      perpetual = (one + discount) / discount
      diskUnitCost = usd_per_gb_month ×ᵤ 1USD / 1GB
      diskTotalCost = perpetual * diskMonthly * diskUnitCost

      iopsMonthly = IO /ᵤ s ‣ nodes * spike ×ᵤ io
      iopsUnitCost = usd_per_iops_month ×ᵤ 1USD / (1IO / 1s)
      iopsTotalCost = iopsMonthly * iopsUnitCost
      
      downstream = egress_downstream ×ᵤ throughput
      upstream   = egress_upstream   ×ᵤ throughput
      egressMonthly = B /ᵤ s ‣ downstream + upstream
      egressUnitCost = usd_per_gb ×ᵤ 1USD / 1GB
      egressTotalCost = egressMonthly * egressUnitCost * 1month

      nic = B /ᵤ s ‣ spike ×ᵤ max upstream downstream

      totalCost = vcpuTotalCost + diskTotalCost + iopsTotalCost + egressTotalCost

      price = usd_per_ada ∷ᵤ USD /ᵤ ADA
      byteFee = ada_per_kb ×ᵤ 1ADA / 1kB
      txFee = txSize * byteFee
      totalFees = txRate * txFee * price * 1month

      fraction = (stake_percent ∷ᵤ unitless) / 1hundred
               * (retained_percent ∷ᵤ unitless) / 1hundred
      retained = fraction * totalFees
      profit = retained - totalCost
      return = retained / totalCost
      
      txCostUsd = totalCost / fraction / txRate / 1month
      txCostAda = txCostUsd / price
      
  in record {
  
       vcpu_per_month         = val (vcpuMonthly     / 1vCPU         )
     ; disk_gb_per_month      = val (diskMonthly     / 1GB           )
     ; iops_per_month         = val (iopsMonthly     / (1IO / 1s)    )
     ; egress_gb_per_month    = val (egressMonthly   / (1GB / 1month))
     ; nic_gb_s_per_month     = val (nic             / (1Gb / 1s)    ) 
     
     ; cpu_usd_per_month      = val (vcpuTotalCost   / 1USD          )
     ; disk_usd_per_month     = val (diskTotalCost   / 1USD          )
     ; iops_usd_per_month     = val (iopsTotalCost   / 1USD          )
     ; egress_usd_per_month   = val (egressTotalCost / 1USD          )
     ; total_usd_per_month    = val (totalCost       / 1USD          )

     ; usd_tx                 = val (txCostUsd       / (1USD / 1tx)  )
     ; ada_tx                 = val (txCostAda       / (1ADA / 1tx)  )

     ; retained_usd_per_month = val (retained        / 1USD          )
     ; profit_usd_per_month   = val (profit          / 1USD          )
     ; return_percent         = val (return          * 1hundred      )

     }
