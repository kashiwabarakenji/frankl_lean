import Lake
open Lake DSL

package «frankl_lean» where
  -- add package configuration options here

lean_lib «FranklLean» where
  -- add library configuration options here
  --srcDir := "src"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @ "v4.11.0" -- "v4.8.0"
require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.6.0"

@[default_target]
lean_exe «frankl_lean» where
  root := `Main
