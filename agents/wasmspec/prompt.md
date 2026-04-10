# wasmspec — Close tryCatch + L17522 noCallFrameReturn sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~3.5GB free. USE LSP ONLY — no builds.

## CONCURRENCY
- proof agent is FIXING BUILD ERRORS in ANFConvertCorrect.lean (L9752-11220)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** work on L16366-16439 (tryCatch) and L17522-17806 (callframe + tryCatch)

## CAUTION: BUILD IS CURRENTLY BROKEN
The proof agent broke ANFConvertCorrect.lean in its last run. There are ~100 errors around L9752-11220. You MUST NOT edit lines in that range. Stay in YOUR zones (L16366+ and L17522+).

Wait for the proof agent to fix the build before testing your changes with `lean_diagnostic_messages`. If the LSP shows errors in your zones that are CASCADING from earlier errors, wait.

## ===== P0: L17522 — noCallFrameReturn =====

```lean
sorry /- noCallFrameReturn: Need catchParam ≠ "__call_frame_return__". -/
```

This should be closable. The proof agent defined `noCallFrameReturn_tryCatch_direct_bridge` at L4303 but it uses `normalizeExpr_tryCatch_decomp` which doesn't exist yet.

**Your job**: Define `normalizeExpr_tryCatch_decomp` or find an alternative path.

The key insight: `normalizeExpr (.tryCatch body cp cb fin) k` normalizes to `.tryCatch body' cp' cb' fin'` where `cp' = cp` (the catch parameter is preserved by normalizeExpr). So if `noCallFrameReturn (.tryCatch body cp cb fin) = true`, then `cp ≠ "__call_frame_return__"`, and since `cp' = cp`, `catchParam ≠ "__call_frame_return__"`.

Try:
1. `lean_goal` at L17522 to see exact proof state
2. If catchParam comes from normalizeExpr, unfold normalizeExpr for tryCatch to show cp is preserved
3. Use `noCallFrameReturn` definition directly

## ===== P1: L16366-16439 (tryCatch step_sim cases) =====

These are in `normalizeExpr_tryCatch_step_sim`:
- **L16366**: tryCatch body-error (body throws, tryCatch catches)
- **L16384**: tryCatch body-step (body takes a step within tryCatch)
- **L16387**: compound tryCatch cases

Use `lean_goal` at each to understand what's needed. The body-error case (L16366) is the most promising:
- Body produced `.error msg` → tryCatch catches → transitions to catch body
- Need to show flat tryCatch catch matches ANF tryCatch catch after normalizeExpr

## ===== P2: L17533 — body_sim IH =====

```lean
sorry /- body_sim: inner simulation IH, needs anfConvert_step_star to be proved by strong induction -/
```

This depends on `anfConvert_step_star` which is the big unsolved theorem. SKIP this — it needs the main induction to be set up first.

## ===== P3: L17753 and L17806 =====

Check what these are with `lean_goal`. If tractable, attempt. If blocked, document why.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
2. Check build status — if broken, WAIT for proof agent to fix
3. `lean_goal` at L17522, L16366, L16384, L17753, L17806
4. Attempt L17522 first (most likely closable)
5. Log what you closed and what's blocked
6. **LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
