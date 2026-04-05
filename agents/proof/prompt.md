# proof — Close tryCatch body-error (L11150) and body-step (L11163)

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

### TASK 1: L11150 — tryCatch body-error (PRIORITY 1)
```lean
sorry -- tryCatch body-error: body_sim + Steps_tryCatch_body_ctx + error catch + SimRel recon
```
Context (L11138-11150): `exprValue? body = none`, `step? body = some (.error msg, sb)`.

**CONCRETE APPROACH — follow this EXACTLY:**
1. `lean_goal` at L11150 to see exact proof state
2. You have `body_sim` (L11032-11040) — apply it to the body step:
   ```lean
   have ⟨sf_b', evs_b, hsteps_b, htrace_b, hsimrel_b, hewf_b⟩ := body_sim sa_body sf_body (.error msg) sa_body' hsimrel_body hewf_body hstep_body
   ```
3. Decompose the flat steps into non-error prefix + final step:
   - The ANF produced `.error msg`, so `observableTrace [.error msg] = observableTrace evs_b`
   - The Flat steps must also produce an error event
4. Lift non-error Flat steps through tryCatch via `Steps_tryCatch_body_ctx` (L1887)
5. For the final error step: Flat.step? on `.tryCatch (.error msg ...) cp cb fin` catches the error
6. Result: Flat transitions to catch handler with error bound to catchParam
7. Construct SimRel for catch handler state

**Key gotcha**: `Steps_tryCatch_body_ctx` requires `hnoerr` (all events are non-error). You need to split the Flat steps into non-error prefix and error suffix BEFORE lifting.

### TASK 2: L11163 — tryCatch body-step (normal step, non-error)
```lean
sorry -- tryCatch body-step: body_sim + Steps_tryCatch_body_ctx + SimRel recon
```
Context (L11151-11163): body took normal step, `step? body = some (t_body, sb)`.

**CONCRETE APPROACH:**
1. Use `body_sim` to get Flat body steps (all non-error since t_body is not .error)
2. ALL events are non-error → lift ALL through `Steps_tryCatch_body_ctx` directly
3. Flat result: `.tryCatch sf_b'.expr catchParam cb_flat fin?`
4. Construct SimRel with the ANF result `.tryCatch sb.expr catchParam catchBody finally_`
5. **Hard part**: need normalizeExpr correspondence between stepped body and catch/finally

### TASK 3: L12249-12250 — noCallFrameReturn + body_sim
L12249 (noCallFrameReturn): should be provable from `hewf` — "__call_frame_return__" is not a valid JS identifier
L12250 (body_sim): needs strong induction, defer unless you can factor

### TASK 4: L12470, L12523 — break/continue compound (LOW PRIORITY)
Skip unless Tasks 1-2 done.

## PRIORITY ORDER
1. L11150 (body-error) — most tractable
2. L11163 (body-step) — similar structure
3. L12249 (noCallFrameReturn) — likely easy
4. Everything else — deferred

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
