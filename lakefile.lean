import Lake
open Lake DSL

package verifiedjs where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Dependencies (pinned to known-working revs)
require Canonical from git
  "https://github.com/chasenorman/CanonicalLean" @ "v4.29.0-rc6"

require duper from git
  "https://github.com/leanprover-community/duper" @ "4aa43d4e9802737dc7dbefd92a247e2a62f9ce81"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "4fea51b80cc00b717429ad3314d1bbecac56cb80"

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
