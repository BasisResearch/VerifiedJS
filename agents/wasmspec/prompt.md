# wasmspec — Close return/yield/structural + tryCatch sorries in ANFConvertCorrect.lean

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~3.5GB free. USE LSP ONLY — no builds.

## CONCURRENCY
- proof agent works on Flat/Semantics.lean + compound sorries (L11765-12257)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own L12288-12318 (return/yield/structural), L16418-16439 (tryCatch), and L17522-17806

## STATUS: Your previous K-mismatch analysis was excellent. ALL 24 if_branch sorries ARE architecturally blocked. REDIRECTING you to new targets.

## ===== P0: CLOSE L12288 and L12292 (return/yield with some val) =====

These are in `normalizeExpr_step_sim` around L12261.

**L12288**: `| some val => sorry -- return (some val): compound, can produce .let`
**L12292**: `| some val => sorry -- yield (some val): compound, can produce .let`

### STRATEGY:
For `return (some val)` where val is compound (not a value):
1. `normalizeExpr (.return (some val)) k` produces something like `.let fresh (normalizeExpr val ...) (.return (some (.trivial fresh)))`
2. The flat expr `.return (some val)` steps val first (L968-970)
3. The ANF `.let fresh ... (.return ...)` steps the init first
4. Show the SimRel is preserved after one step of val

Use `lean_goal` at L12288 to see exact proof state. Then try:
```lean
sorry -- first try lean_goal to see what we need
```

If the goal is about SimRel reconstruction after stepping val:
1. Use the normalizeExpr decomposition for return/yield
2. Apply the IH on the sub-expression val
3. Reconstruct the SimRel with the new state

### CONCRETE STEPS:
1. `lean_goal` at L12288 (column at the sorry)
2. `lean_goal` at L12292
3. If goals are tractable, attempt closure
4. If blocked, document WHY in sorry comment

## ===== P1: CLOSE L16418, L16436, L16439 (tryCatch cases) =====

**L16418**: `sorry -- tryCatch body-error: remaining gap is lifting body steps through tryCatch context`
**L16436**: `sorry -- tryCatch body-step: blocked by callStack propagation + counter alignment`
**L16439**: `| _ => sorry -- compound cases: deferred`

### STRATEGY for L16418:
In the tryCatch body-error case, the body produced an `.error` event. The flat tryCatch should catch this and step to the catch body. The key is showing that:
1. Flat tryCatch catches the error (Flat.step? on tryCatch with error event)
2. The catch body normalization matches
3. SimRel is preserved

Use `lean_goal` at L16418 to see the exact state.

### STRATEGY for L16436:
TryCatch body is stepping (not yet a value or error). The flat tryCatch wraps the body step. Need to show callStack is preserved and the counter aligns.

### STRATEGY for L16439:
This is a catch-all for compound tryCatch head cases. Low priority — skip if L16418 and L16436 are hard.

## ===== P2: INVESTIGATE L17522-17533 and L17753-17806 =====

**L17522**: `sorry /- noCallFrameReturn: Need catchParam ≠ "__call_frame_return__". -/`
**L17533**: `sorry /- body_sim: inner simulation IH, needs anfConvert_step_star to be proved by strong induction -/`
**L17753**: `sorry`
**L17806**: `sorry`

Check if L17522 is closable — it needs to show a catch parameter isn't equal to a specific string. This might be derivable from a well-formedness condition.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
2. `lean_goal` at L12288, L12292, L16418, L16436, L17522
3. Attempt to close the easiest goals first
4. Log what you closed and what's still blocked
5. **LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
