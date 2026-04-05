# proof — Close L12429 (noCallFrameReturn) then L11330 (body-error)

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
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

## CURRENT STATE — 47 ANF sorries. Your zone has 7 sorries:
- L11330: tryCatch body-error
- L11343: tryCatch body-step
- L11346: tryCatch compound (deferred)
- L12429: noCallFrameReturn
- L12430: body_sim IH
- L12650: break compound
- L12703: continue compound

### TASK 1: L12429 — noCallFrameReturn (EASIEST — DO FIRST)
```lean
(sorry /- noCallFrameReturn: source tryCatch params are never "__call_frame_return__" -/)
```
"__call_frame_return__" is a synthetic name from closure conversion — never in source JS.
The `hsupp` hypothesis or `hewf` should establish this. Try:
```lean
lean_goal at L12429 column 7
lean_multi_attempt at L12429 column 7
["by simp [noCallFrameReturn]", "by intro h; exact absurd h (by decide)", "by exact hncf"]
```
If no precondition exists, add `noCallFrameReturn` as a predicate on source programs and propagate.

### TASK 2: L11330 — tryCatch body-error (PRIORITY 1)
```lean
sorry -- tryCatch body-error: body_sim + Steps_tryCatch_body_ctx + error catch + SimRel recon
```
KEY INSIGHT: After body errors, tryCatch CATCHES and transitions to catch handler. The catch handler is a FRESH normalizeExpr — you DON'T need counter alignment!

**Approach:**
1. Get Flat body steps from `body_sim`
2. Split into non-error prefix + final error event
3. Lift non-error prefix through tryCatch via `Steps_tryCatch_body_ctx`
4. Final error: `.tryCatch (.error msg ..) cp cb fin` catches → `cb[cp := msg]`
5. SimRel for catch: use `hcatch_norm` with error value substituted

### TASK 3: L11343 — tryCatch body-step (defer if counter alignment blocks it)

### DO NOT TOUCH: L12650, L12703 (break/continue — architecturally blocked)

## PRIORITY ORDER
1. L12429 (noCallFrameReturn) — likely 5 min
2. L11330 (body-error) — fresh catch handler avoids counter alignment
3. L11343 (body-step) — defer if stuck
4. L12430 (body_sim IH) — needs strong induction, defer

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
