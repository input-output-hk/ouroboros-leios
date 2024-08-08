import Lake
open Lake DSL

package «Leios» where

lean_lib «Leios» where
  srcDir := "src"

@[default_target]
lean_exe «leios» where
  root := `Main
  srcDir := "src"
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
