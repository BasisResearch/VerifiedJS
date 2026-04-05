# proof — Close tryCatch body-error (L11344) and body-step (L11357)

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.4GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L8000-10912 (if compound/eval context lifting)
- **YOU** own L11200-11360 (tryCatch) and L12400-12717 (break/continue/return)
- DO NOT touch lines outside your range

## CURRENT STATE — 47 ANF sorries. Your zone has 7 sorries.

### YOUR KEY INSIGHT FROM LAST RUN:
Counter-alignment is the core blocker for body-error and body-step. `normalizeExpr` with trivial k produces counter-dependent fresh names, so SimRel reconstruction fails after body-step.

### TASK 1: L12443 — noCallFrameReturn (EASIEST — DO THIS FIRST)
```lean
(sorry /- noCallFrameReturn: source tryCatch params are never "__call_frame_return__" -/)
```
**Strategy**: "__call_frame_return__" is a synthetic name that never appears in source JS. The `hsupp` hypothesis (or `hewf`) should establish this. Try:
```lean
lean_multi_attempt at L12443 column 7
["by simp [noCallFrameReturn]", "by intro h; exact absurd h (by decide)", "by exact hncf"]
```
Check what `noCallFrameReturn` requires and whether there's an invariant on source catch params.

### TASK 2: L11344 — tryCatch body-error (PRIORITY 1)
```lean
sorry -- tryCatch body-error: body_sim + Steps_tryCatch_body_ctx + error catch + SimRel recon
```
**Counter-alignment workaround**: Instead of trying to reconstruct a full SimRel after body-error, consider:
1. After body produces `.error msg`, the tryCatch CATCHES and transitions to catch handler
2. The catch handler is a FRESH normalizeExpr call (not dependent on body's counter state)
3. So you don't need counter alignment — you need to construct SimRel for the catch handler from scratch
4. The catch handler's SimRel comes from `hcatch_norm` (the normalization of the catch body)

**Concrete approach**:
1. Get Flat body steps from `body_sim`
2. Split into non-error prefix + final error event
3. Lift non-error prefix through tryCatch via `Steps_tryCatch_body_ctx` (requires hnoerr)
4. Final error step: `.tryCatch (.error msg ..) cp cb fin` catches → transitions to `cb[cp := msg]`
5. SimRel for catch: use `hcatch_norm` with the error value substituted for catchParam

### TASK 3: L11357 — tryCatch body-step (normal step)
Same structure as body-error but simpler (all events are non-error, lift everything through Steps_tryCatch_body_ctx).

**The counter-alignment issue IS real here** — body-step needs to show the stepped body still has a valid normalizeExpr correspondence. Consider:
- Can you reformulate SimRel to use `sf.expr.depth` decreasing instead of exact counter match?
- Or: defer this and focus on body-error which avoids the issue

### TASK 4: L12664, L12717 — break/continue compound
These require Flat.step? error propagation — architecturally blocked. Skip for now.

## PRIORITY ORDER
1. L12443 (noCallFrameReturn) — likely 5 min
2. L11344 (body-error) — catch handler SimRel doesn't need counter alignment
3. L11357 (body-step) — hardest, counter alignment needed
4. L12444 (body_sim IH) — needs strong induction redesign, defer

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
