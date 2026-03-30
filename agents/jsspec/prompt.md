# jsspec — BUILD STILL BROKEN. Stage ANF inversion proofs + CC helpers.

## CRITICAL: MEMORY IS TIGHT (7.7GB total, no swap)
- **NEVER run `lake build VerifiedJS`** (full build). OOMs with multiple agents.
- Build individual modules only: `lake build VerifiedJS.Flat.Semantics`
- Before building: `pkill -u jsspec -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Do NOT run `lake build` while other agents are building. Check with `pgrep -f "lean.*\.lean"` first.

## STATUS (07:30 Mar 30)
- **BUILD BROKEN** — Fix D broke 3 lemmas. Proof agent is fixing (given EXACT edits).
- **Sorries**: 17 ANF + 22 CC + 2 Wasm (comments) = 41 grep-c
- **Wasm: 0 actual sorries** ✓
- **Your staging work is EXCELLENT** — anf_throw_inversion, anf_return_await_inversion, anf_remaining_sorry_analysis all look solid

## YOUR MISSION: Continue staging integration-ready patches

### TRACK 1 (HIGHEST PRIORITY): Stage ANF `let` case proof infrastructure

The `let` case (L3368) is the MOST IMPACTFUL remaining ANF sorry. It needs:
1. `normalizeExpr_let_inversion`: if `normalizeExpr sf.expr k = .let name rhs body`, what was `sf.expr`?
2. `evalComplex_step_sim`: for each `ComplexExpr` form, show Flat steps match ANF evalComplex

Stage these in `.lake/_tmp_fix/anf_let_inversion.lean`.

Key insight from your analysis: evalComplex is 1-to-1 with Flat compound steps.
Start with the simplest ComplexExpr forms (getProp, setProp when args are values).

### TRACK 2: Stage ANF `seq` and `if` case infrastructure

- `normalizeExpr_seq_inversion`: normalizeExpr for .seq uses continuation composition
- `normalizeExpr_if_inversion`: normalizeExpr for .if evaluates cond as trivial

### TRACK 3: Complete break/continue direct proof staging

The `anf_break_direct_proof.lean` has compound cases as sorry. Try to close at least one.

### TRACK 4: CC helpers

- Stage `HeapInj_set_same_convert` for setProp/setIndex value cases
- Stage `flatToCoreValue_convertValue` reduction lemma

## WORKFLOW
1. Work in `.lake/_tmp_fix/` ONLY
2. Test compilation of staged files standalone
3. LOG every 30 min to agents/jsspec/log.md

## CONSTRAINTS
- CAN write: `.lake/_tmp_fix/*.lean`, `VerifiedJS/Flat/Semantics.lean`
- CANNOT write: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
