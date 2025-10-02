
import Cli
import Linleios
import Parser.Char.Numeric
import Parser.Stream

open Cli
open Lean (Json)


instance : ParseableType Float where
  name     := "Float"
  parse? x := match (Parser.Char.ASCII.parseFloat : SimpleParser Substring Char Float).run x with
              | .ok _ y => some y
              | _       => none


def runMarkovCmd (p : Parsed) : IO UInt32 :=
  do
    let activeSlotCoefficient : Float := p.flag! "active-slot-coefficient" |>.as! Float
    let Lheader : Nat := p.flag! "l-header" |>.as! Nat
    let Lvote : Nat := p.flag! "l-vote" |>.as! Nat
    let Ldiff : Nat := p.flag! "l-diff" |>.as! Nat
    let committeeSize : Nat := p.flag! "committee-size" |>.as! Nat
    let τ : Float := p.flag! "quorum-fraction" |>.as! Float
    let pRbHeaderArrives : Float := p.flag! "p-rb-header-arrives" |>.as! Float
    let pEbValidates : Float := p.flag! "p-eb-validates" |>.as! Float
    let pLateDiffusion : Float := p.flag! "p-late-diffusion" |>.as! Float
    let fAdversary : Float := p.flag! "adversary-fraction" |>.as! Float
    let ε : Float := p.flag! "tolerance" |>.as! Float
    let rbCount : Nat := p.flag! "rb-count" |>.as! Nat
    let env := makeEnvironment Lheader Lvote Ldiff activeSlotCoefficient committeeSize.toFloat τ pRbHeaderArrives pEbValidates pLateDiffusion fAdversary
    let sn := simulate env default ε rbCount
    if p.hasFlag "output-file"
      then IO.FS.writeFile (p.flag! "output-file" |>.as! String) (Json.pretty $ ebDistributionJson sn)
    IO.println s!"RB efficiency: {(reprPrec (rbEfficiency sn) 0).pretty}"
    IO.println s!"EB efficiency: {(reprPrec (ebEfficiency sn) 0).pretty}"
    IO.println s!"Overall efficiency: {(reprPrec (efficiency sn) 0).pretty}"
    IO.eprintln s!"Missing probability: {1 - totalProbability sn}"
    pure 0

def markov : Cmd := `[Cli|
  markov VIA runMarkovCmd; ["0.0.1"]
  "Run a Markov simulation of Linear Leios."
  FLAGS:
    "active-slot-coefficient" : Float  ; "The active slot coefficient for RBs, in probability per slot."
    "l-header"                : Nat    ; "L_header protocol parameter, in slots."
    "l-vote"                  : Nat    ; "L_vote protocol parameter, in slots."
    "l-diff"                  : Nat    ; "L_diff protocol parameter, in slots."
    "committee-size"          : Nat    ; "Expected number of voters in the committee, out of 2500 stakepools total."
    "quorum-fraction"         : Float  ; "τ protocol parameter, in %/100."
    "p-rb-header-arrives"     : Float  ; "Probability that the RB header arrives before L_header."
    "p-eb-validates"          : Float  ; "Probability that the EB is fully validated before 3 L_header + L_vote."
    "p-late-diffusion"        : Float  ; "Probability than a RB producer hasn't validated the previous EB."
    "adversary-fraction"      : Float  ; "Fraction of stake that is adversarial: the adversary never produces RBs or EBs and never votes."
    "tolerance"               : Float  ; "Discard states with less than this probability."
    "rb-count"                : Nat    ; "Number of potential RBs to simulate."
    "output-file"             : String ; "Path to the JSON output file for the EB distribution."
  EXTENSIONS:
    defaultValues! #[
      ("active-slot-coefficient", "0.05")
    , ("l-header"               , "1"   )
    , ("l-vote"                 , "4"   )
    , ("l-diff"                 , "7"   )
    , ("committee-size"         , "600" )
    , ("quorum-fraction"        , "0.75")
    , ("p-rb-header-arrives"    , "0.95")
    , ("p-eb-validates"         , "0.90")
    , ("p-late-diffusion"       , "0.05")
    , ("adversary-fraction"     , "0"   )
    , ("tolerance"              , "1e-8")
    , ("rb-count"               , "100" )
    ]
]

def main (args : List String) : IO UInt32 :=
  markov.validate args
