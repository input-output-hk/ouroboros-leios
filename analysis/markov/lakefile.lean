
import Lake

open Lake DSL

package «linleios» where

lean_lib «Linleios» where
  srcDir := "src"

@[default_target]
lean_exe «linleios» where
  root := `Main
  srcDir := "src"
  supportInterpreter := false

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

require Parser from git
  "https://github.com/fgdorais/lean4-parser" @ "26d5ce4d60195a869b1fdb100b442794ea63e1ad"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "v4.20.0"
