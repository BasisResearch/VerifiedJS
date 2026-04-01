# proof — Build HasReturnInHead + HasYieldInHead, prove return/yield_step_sim

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 19 sorries. Lower 0 ✓. CC — OTHER AGENTS OWN IT.

## EXCELLENT PROGRESS: HasAwaitInHead DONE ✓
You built HasAwaitInHead + normalizeExpr_await_or_k + normalizeExpr_await_implies_hasAwaitInHead (440 lines).
await_step_sim partially proved: await_direct base cases done, 2 sorries remain (compound + non-direct).
This is GREAT. Now replicate for return and yield.

## YOUR NEXT TASK: Build HasReturnInHead + HasYieldInHead

### Priority 1: normalizeExpr_return_step_sim (L4694)
This is a full `sorry`. Apply the SAME pattern as await_step_sim:
1. Build `HasReturnInHead` (copy HasAwaitInHead, replace await_direct with return_none_direct + return_some_direct)
2. Build `normalizeExpr_return_or_k` (copy normalizeExpr_await_or_k)
3. Build `normalizeExpr_return_implies_hasReturnInHead`
4. Decompose return_step_sim into HasReturnInHead case analysis

Note: return has TWO sub-cases: `arg = none` and `arg = some t`. Both need handling.

### Priority 2: normalizeExpr_yield_step_sim (after return is decomposed)
Same pattern for yield.

### Priority 3: Compound cases in await_step_sim (L4660, L4663)
These need depth induction on normalizeExpr for compound expressions inside await.

## DO NOT ATTEMPT:
- GROUP B (L4298, L4329, L4340, L4418, L4449, L4460, L4477) — architecturally blocked
- hasBreakInHead/hasContinueInHead (L4494, L4507) — potentially unprovable as stated

## CURRENT ANF SORRY LOCATIONS (file is 6786 lines):
```
GROUP B (SKIP): L4298, L4329, L4340, L4418, L4449, L4460, L4477
hasBreak/ContinueInHead: L4494, L4507
await compound: L4660, L4663
return_step_sim: L4694 (YOUR TARGET)
await helpers + step_sim decomposed: L4887, L4890
seq/if/let/tryCatch_step_sim: L4921, L4942, L4963, L4984, L5005
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
