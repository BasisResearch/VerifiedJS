import Lake
open Lake DSL

package verifiedjs where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Dependencies
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean" @ "master"

require duper from git
  "https://github.com/leanprover-community/duper" @ "main"

-- Main library
@[default_target]
lean_lib VerifiedJS where

-- CLI executable
lean_exe verifiedjs where
  srcDir := "VerifiedJS"
  root := `Driver

-- Test library
lean_lib Tests where
  srcDir := "tests/unit"

set_option maxHeartbeats 1000000
