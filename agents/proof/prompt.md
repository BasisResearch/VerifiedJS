# proof — Close tryCatch body-error (L10548) and body-step (L10551), then call-frame (L10492/10529)

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L7700-9912 (if compound/eval context lifting)
- **YOU** own L10400-10555 (tryCatch) and L11840-11910 (break/continue)
- DO NOT touch lines outside your range

## CURRENT STATE — tryCatch lit-body cases PROVED, 5 sorries remain in your zone

### TASK 1: L10548 — tryCatch body-error (PRIORITY 1)
```lean
sorry -- tryCatch body-error: needs inner body step simulation + catch handler SimRel
```
Context (L10543-10548): `exprValue? body = none`, `step? body = some (.error msg, sb)`.

**Strategy**:
1. `lean_goal` at L10548 to see exact state
2. You have `hbody_norm` (normalizeExpr for body) and inner SimRel from it
3. body errors → ANF unwraps tryCatch, binds error to catch variable
4. Flat.step? on tryCatch also: steps body, body errors → steps to catch handler with error substituted
5. Both sides produce catch handler with error bound to catchParam
6. Construct SimRel for the resulting catch handler states
7. Key: use `normalizeExpr_step_sim` (or similar inner IH) to get Flat body → error, then show tryCatch catches it

### TASK 2: L10551 — tryCatch body-step (normal step, non-value, non-error)
```lean
sorry -- tryCatch body-step: needs inner body step simulation + tryCatch wrapping SimRel
```
Context (L10549-10551): body took a normal step, `step? body = some (t_body, sb)` where t_body is NOT error.

**Strategy**:
1. `lean_goal` at L10551
2. Inner body step: use SimRel/IH to get corresponding Flat step on body
3. Both ANF and Flat wrap the stepped body back in tryCatch
4. Construct SimRel for `.tryCatch stepped_body catchParam cb finally_` on both sides

### TASK 3: L10492, L10529 — call frame contradiction (EASY)
```lean
sorry -- call frame: shouldn't occur in source programs
```
These are where `catchParam = "__call_frame_return__"`. This should be contradicted by well-formedness of source programs.

**Strategy**:
1. `lean_goal` at L10492
2. Look for an `ExprWellFormed` or similar hypothesis that excludes internal catch params
3. If not available, check if you can derive contradiction from `supported` or other invariants
4. If truly no hypothesis available, add a precondition to `normalizeExpr_tryCatch_step_sim`

### TASK 4: L10554 — compound cases (ONLY if 1-3 done)
```lean
| _ => sorry -- compound cases: deferred
```
Needs eval context lifting. Same systemic blocker as ~17 other sorries. Low priority.

## PRIORITY ORDER
1. L10548 (body-error) — most tractable, should compose from inner SimRel
2. L10551 (body-step) — similar structure
3. L10492/10529 (call frame) — should be easy contradiction
4. L10554 (compound) — only if time permits

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
