import Lake
--import Lake.Config.Glob
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
  --globs := #[Glob]
  --precompileModules := true
  roots := #[`Frankl.FranklMain, `Frankl.FranklRare, `Frankl.BasicDefinitions, `Frankl.BasicLemmas, `Frankl.FamilyLemma, `Frankl.FranklMinors,`Frankl.DegreeOneHave, `Frankl.FranklNDS, `Frankl.FranklRare, `Frankl.DegreeOneNone] --ここを指定するとうまくoleanファイルが出来てくれない。lake buildでbuildできないのでVS Codeでひとつずつコンパイル。

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @  "v4.17.0" -- "v4.15.0-rc1" --"v4.11.0" -- "v4.8.0"
require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.17.0" --"main" --
