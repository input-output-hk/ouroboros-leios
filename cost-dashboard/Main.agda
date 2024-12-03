{-# OPTIONS --guardedness #-}


module Main where


open import Agda.Builtin.Float using (Float ; primShowFloat)
open import Data.List using (_∷_)
open import CostModel using (Scenario ; Result ; calculate)
open import Agda.Builtin.String renaming (primStringAppend to _++_)

open import IO


baseScenario : Scenario
baseScenario = 
  record {

    slots_per_s             = 1.0
  ; phase_per_pipeline      = 5.0
  ; slot_per_pipeline       = 20.0

  ; praos_tx_per_s          = 1.0
  ; leios_tx_per_s          = 100.0
  ; kb_per_tx               = 1.940
  ; verify_vcpu_ms_per_tx   = 1.50

  ; ib_per_slot             = 0.25
  ; io_per_ib               = 200.0
  ; build_vcpu_ms_per_ib    = 300.0
  ; verify_vcpu_ms_per_ib   = 100.0
   
  ; eb_per_pipeline         = 1.0
  ; io_per_eb               = 10.0
  ; build_vcpu_ms_per_eb    = 300.0
  ; verify_vcpu_ms_per_eb   = 100.0

  ; vote_per_pipeline       = 500.0
  ; kb_per_vote             = 0.725
  ; io_per_vote             = 2.0
  ; build_vcpu_ms_per_vote  = 0.01
  ; verify_vcpu_ms_per_vote = 0.005

  ; cert_per_pipeline       = 1.0
  ; kb_per_cert             = 30.0
  ; io_per_cert             = 100.0
  ; build_vcpu_ms_per_cert  = 100.0
  ; verify_vcpu_ms_per_cert = 50.0

  ; rb_per_slot             = 0.05
  ; kb_per_ibref            = 1.2
  ; io_per_rb               = 100.0  -- NB: Copied from `io_per_cert`
  ; build_vcpu_ms_per_rb    = 300.0
  ; verify_vcpu_ms_per_rb   = 100.0
  ; ledger_gb               = 200.0

  ; egress_downstream       = 25.0
  ; egress_upstream         = 1.5
  ; spike                   = 5.0
  ; producers               = 1.0
  ; relays                  = 2.0
  ; stake_percent           = 0.1
  ; retained_percent        = 20.92

  ; usd_per_ada             = 0.75
  ; ada_per_kb              = 0.17401
    
  ; discount_annual_percent = 15.0
  ; compression_percent     = 75.0

  ; usd_per_vcpu_month      = 20.0
  ; usd_per_gb_month        = 0.12
  ; usd_per_iops_month      = 0.05
  ; usd_per_gb              = 0.10

  }


main : Main
main =
  let open Result (calculate baseScenario)
  in run (
    do

      putStrLn "Resources"
      putStrLn ("  Compute: "           ++ (primShowFloat vcpu_per_month      ++ " vCPU/month"))
      putStrLn ("  Disk: "              ++ (primShowFloat disk_gb_per_month   ++ " GB/month"  ))
      putStrLn ("  IOPS: "              ++ (primShowFloat iops_per_month      ++ " IO/s/month"))
      putStrLn ("  Network egress: "    ++ (primShowFloat egress_gb_per_month ++ " GB/month"  ))
      putStrLn ("  Network interface: " ++ (primShowFloat nic_gb_s_per_month  ++ " Gb/s/month"))

      putStrLn "Costs"
      putStrLn ("  Compute: "          ++ (primShowFloat cpu_usd_per_month    ++ " USD/month"))
      putStrLn ("  Disk (amortized): " ++ (primShowFloat disk_usd_per_month   ++ " USD/month"))
      putStrLn ("  IOPS: "             ++ (primShowFloat iops_usd_per_month   ++ " USD/month"))
      putStrLn ("  Network egress: "   ++ (primShowFloat egress_usd_per_month ++ " USD/month"))
      putStrLn ("  Total: "            ++ (primShowFloat total_usd_per_month  ++ " USD/month"))

      putStrLn "Metrics"
      putStrLn ("  Cost per transaction: " ++ (primShowFloat usd_tx                 ++ " USD/tx"   ))
      putStrLn ("  Cost per transaction: " ++ (primShowFloat ada_tx                 ++ " ADA/tx"   ))
      putStrLn ("  Retained fees: "        ++ (primShowFloat retained_usd_per_month ++ " USD/month"))
      putStrLn ("  Retained fees − cost: " ++ (primShowFloat profit_usd_per_month   ++ " USD/month"))
      putStrLn ("  Retained fees ÷ cost: " ++ (primShowFloat return_percent         ++ " %"        ))

  )
