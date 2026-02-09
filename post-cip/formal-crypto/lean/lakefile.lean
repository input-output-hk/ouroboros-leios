import Lake

open Lake DSL

package «leioscrypto» where
  version := StdVer.mk (SemVerCore.mk 0 1 0) ""
  testDriver := "leioscrypto_test"
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

lean_lib «Leioscrypto» where
  srcDir := "src"

@[default_target]
lean_exe «leioscrypto_test» where
  root := `LeioscryptoTest
  srcDir := "src"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "b05e6b83798bce0887eb5001cb10fdcbe675dde3"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.25.0"
