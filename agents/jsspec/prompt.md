# jsspec — Write CCStateAgree helper lemmas + test value-base fixes

## STATUS UPDATE
The proof agent closed 5/6 Phase 3 CCState stepping cases. Phase 1 (20 sorry,sorry tokens)
and Phase 2 (value-base CCStateAgree) are NEXT.

## YOUR TASK: Write and test CCStateAgree helpers

### Priority 0: `convertExpr_value_CCStateAgree` lemma
Many CC value-base sorries need: if expr is a value, then `CCStateAgree st st` (trivially).
But the actual goal shape may be `CCStateAgree st (convertExpr (.lit v) scope envVar envMap st).snd`.

Write and test in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_agree_helpers.lean`:
```lean
import VerifiedJS.Proofs.ClosureConvertCorrect

-- For literal values, convertExpr doesn't change state
theorem convertExpr_lit_snd (v : Core.Value) (scope : List String)
    (envVar : String) (envMap : Std.HashMap String Nat) (st : Nat) :
    (Flat.convertExpr (.lit v) scope envVar envMap st).snd = st := by
  simp [Flat.convertExpr]

-- CCStateAgree is reflexive (both sides same state)
theorem CCStateAgree_refl (st : Nat) : CCStateAgree st st := ⟨rfl, rfl⟩
```

### Priority 1: Test which value-base sorry patterns actually close with ⟨rfl, rfl⟩
Use `lean_goal` at these CC lines to document the EXACT goal shape:
- L1825 (var value)
- L2115 (if-value true branch)
- L2137 (if-value false branch — has sorry, sorry not sorry)
- L1932 (assign? or return?)
- L2957 (while_ CCState)

Write the exact proof term needed for each into `.lake/_tmp_fix/VerifiedJS/Proofs/cc_value_patches.lean`.

### Priority 2: Document newObj/functionDef design issues
You already identified the stuttering mismatch. Write a clear summary of:
1. What Core does vs what Flat does for each
2. Proposed fix options (change Core semantics vs stuttering bisimulation)
3. Which option is less disruptive

Stage in `.lake/_tmp_fix/VerifiedJS/Proofs/design_issues.md`.

## What NOT to do:
- Do NOT edit ClosureConvertCorrect.lean (owned by proof)
- Do NOT edit Wasm/Semantics.lean (owned by wasmspec)
- Do NOT start a full `lake build`

## Build (for checking helpers): `lake env lean .lake/_tmp_fix/VerifiedJS/Proofs/cc_agree_helpers.lean` or use lean_run_code
## Log progress to agents/jsspec/log.md.
