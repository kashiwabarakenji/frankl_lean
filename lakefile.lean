import Lake
open Lake DSL

package «Frankl» where
  -- add package configuration options here
    --srcDir := "Frankl"

    moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
    ]

@[default_target]
lean_lib «Frankl» where
 -- add library configuration options here
  srcDir := "."
  roots := #[`Frankl.FranklMain] --ここを指定するとうまくoleanファイルが出来てくれない。lake buildでbuildできないのでVS Codeでひとつずつコンパイル。

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @  "v4.16.0" -- "v4.15.0-rc1" --"v4.11.0" -- "v4.8.0"
require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.16.0" --"main" --
