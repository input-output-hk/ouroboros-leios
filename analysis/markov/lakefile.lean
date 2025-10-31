import Lake

open Lake DSL

package «linleios» where
  version := StdVer.mk (SemVerCore.mk 0 1 0) ""
  testDriver := "linleios_test"
  leanOptions := #[
    -- pretty-prints `fun a ↦ b`
    ⟨`pp.unicode.fun, true⟩,
    -- disables automatic implicit arguments
    ⟨`autoImplicit, false⟩,
    -- suppresses the checkBinderAnnotations error/warning
    ⟨`checkBinderAnnotations, false⟩,
  ]
  moreServerOptions := #[
    ⟨`trace.debug, true⟩,
  ]

lean_lib «Linleios» where
  srcDir := "src"

@[default_target]
lean_exe «linleios» where
  root := `Main
  srcDir := "src"
  supportInterpreter := false

lean_exe «linleios_test» where
  root := `LinleiosTest
  srcDir := "src"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "24cceb69c20fadca0fd3acabe39fa9270dfb47e6"

require Parser from git
  "https://github.com/fgdorais/lean4-parser" @ "26d5ce4d60195a869b1fdb100b442794ea63e1ad"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "v4.20.0"
