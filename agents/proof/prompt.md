# proof — Prove yield_step_sim then let/seq/if/tryCatch_step_sim

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 21 sorries. Lower 0 ✓. CC — OTHER AGENTS OWN IT.

## YOUR IMMEDIATE TASK: normalizeExpr_yield_step_sim (L5841)

This is the EXACT SAME PATTERN as normalizeExpr_return_step_sim. You already have:
- HasReturnInHead + normalizeExpr_return_implies_hasReturnInHead
- normalizeExpr_return_step_sim with partial proof (L5634, L5637 still sorry)

For yield: Build `HasYieldInHead` + `normalizeExpr_yield_or_k` + `normalizeExpr_yield_implies_hasYieldInHead`.
Copy the HasReturnInHead infrastructure directly, replacing `.return` with `.yield`.

Then the proof follows the same structure:
1. Get `HasYieldInHead sf.expr` from `normalizeExpr_yield_implies_hasYieldInHead`
2. Case split on the inductive
3. Direct cases: `yield_none_direct`, `yield_some_direct` — use `Flat.step?` unfolding
4. Compound cases: sorry (same as return compound cases)

This should CLOSE the monolithic yield_step_sim sorry by decomposing into specific cases.

## PRIORITY 2: let_step_sim (L5862)

The let case should be relatively simple:
- `normalizeExpr` produces `.let name rhs body` → this comes from wrapping sub-expressions
- ANF.step? on `.let` evaluates the complex RHS → need to show Flat steps simulate
- Key: use `normalizeExpr` inversion to find which source expression produced the `.let`

## PRIORITY 3: seq_step_sim (L5883), if_step_sim (L5904), tryCatch_step_sim (L5925)

Same pattern as let — invert normalizeExpr to find source, then simulate.

## DO NOT ATTEMPT:
- Compound cases in return/await (L5118-5298, L5481-5484, L5634, L5637, L5800, L5807, L5810) — these all need depth induction, do them LAST
- hasBreak/ContinueInHead (L5315, L5328) — potentially unprovable

## CURRENT ANF SORRY LOCATIONS (file is 7706 lines):
```
Decomposed await inner value/compound: L5118, L5150, L5161, L5239, L5270, L5281, L5298
hasBreak/ContinueInHead: L5315, L5328
await flat_arg compound: L5481, L5484
return compound cases: L5634, L5637
await this-none semantic mismatch: L5800
await compound inner_arg: L5807, L5810
yield_step_sim: L5841 (YOUR #1 TARGET)
let_step_sim: L5862 (YOUR #2 TARGET)
seq_step_sim: L5883 (YOUR #3 TARGET)
if_step_sim: L5904
tryCatch_step_sim: L5925
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
