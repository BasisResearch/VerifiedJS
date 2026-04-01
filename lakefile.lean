import Lake
open Lake DSL

package verifiedjs where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "4fea51b80cc00b717429ad3314d1bbecac56cb80"

@[default_target]
lean_lib VerifiedJS where

lean_exe verifiedjs where
  srcDir := "VerifiedJS"
  root := `Driver

lean_lib Tests where
  srcDir := "tests/unit"

lean_exe leansplitter where
  srcDir := "tools"
  root := `LeanSplitter

set_option maxHeartbeats 1000000
