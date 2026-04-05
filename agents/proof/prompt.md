# proof — Close tryCatch body-error (L11149) and body-step (L11162)

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.5GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L7700-10720 (if compound/eval context lifting)
- **YOU** own L11023-11165 (tryCatch) and L12240-12522 (break/continue/return)
- DO NOT touch lines outside your range

## CURRENT STATE — 34 ANF sorries. Your zone has 7 sorries.

### TASK 1: L11149 — tryCatch body-error (PRIORITY 1)
```lean
sorry -- tryCatch body-error: body_sim + Steps_tryCatch_body_ctx + error catch + SimRel recon
```
Context (L11137-11149): `exprValue? body = none`, `step? body = some (.error msg, sb)`.

**Strategy**:
1. `lean_goal` at L11149 to see exact state
2. You have `body_sim` (inner simulation IH) in scope from L11031
3. Apply `body_sim` to the ANF body step to get Flat body stepping to error
4. Use `Steps_tryCatch_body_ctx` (L1887) to lift the non-error prefix steps through tryCatch
5. Then show Flat tryCatch catches the error: `step?_tryCatch_body_error` or unfold Flat.step? for error case
6. Both sides transition to catch handler with error bound to catchParam
7. Construct SimRel for catch handler states

**Key infrastructure already available:**
- `Steps_tryCatch_body_ctx` at L1887: lifts multi-step through `.tryCatch [·] cp cb fin`
- `body_sim` parameter at L11031: gives inner simulation for body subexpression
- The `hnoerr` condition on Steps_tryCatch_body_ctx requires showing all events before the error are non-error — decompose the body steps into non-error prefix + final error step

### TASK 2: L11162 — tryCatch body-step (normal step, non-error)
```lean
sorry -- tryCatch body-step: body_sim + Steps_tryCatch_body_ctx + SimRel recon
```
Context (L11150-11162): body took a normal step, `step? body = some (t_body, sb)`.

**Strategy**:
1. `lean_goal` at L11162
2. Use `body_sim` to get Flat body steps
3. ALL events are non-error (since ANF step produced non-error t_body)
4. Lift ALL steps through tryCatch via `Steps_tryCatch_body_ctx`
5. Flat result: `.tryCatch sf_b'.expr catchParam cb_flat fin?`
6. Construct SimRel: ANF has `.tryCatch sb.expr catchParam catchBody finally_`
7. Need to show normalizeExpr on the Flat tryCatch with stepped body matches ANF state

### TASK 3: L12248-12249 — noCallFrameReturn + body_sim (in anfConvert_step_star)
```lean
(sorry /- noCallFrameReturn: source tryCatch params are never "__call_frame_return__" -/)
(sorry /- body_sim: inner simulation IH, needs anfConvert_step_star to be proved by strong induction -/)
```
L12248 should be provable from `hewf` (well-formedness of source expression). Check if `ExprWF` or `supported` excludes "__call_frame_return__" as a catch param.
L12249 needs the overall strong induction — this is a structural dependency, defer unless you can factor it.

### TASK 4: L12469, L12522 — break/continue compound (LOW PRIORITY)
Same eval context lifting blocker. Skip unless Tasks 1-2 done.

## PRIORITY ORDER
1. L11149 (body-error) — most tractable, compose from body_sim + ctx lifting
2. L11162 (body-step) — similar structure
3. L12248 (noCallFrameReturn) — likely easy from well-formedness
4. Everything else — deferred

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
