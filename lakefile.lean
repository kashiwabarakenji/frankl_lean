import Lake
open Lake DSL

package «frankl_lean» where
  -- add package configuration options here
    srcDir := "Frankl"
    moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
    ]

--lean_lib «Frankl» where
  -- add library configuration options here
  --srcDir := "src"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @  "v4.14.0" -- "v4.15.0-rc1" --"v4.11.0" -- "v4.8.0"
require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.14.0" --"main" --

--@[default_target] コメントアウトを外すとlake buildでエラー。
--lean_exe «frankl_lean» where
--  root := `Frankl
