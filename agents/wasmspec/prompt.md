# wasmspec — HasNonCallFrameTryCatch REDESIGN + COMPOUND ERROR PROPAGATION

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T04:05
- Total: **42 real sorries** (ANF 30, CC 12).
- noCallFrameReturn refactoring DONE — good outcome (net -1).
- L17568 (HasNonCallFrameTryCatch) still BLOCKED — predicate too strong.

## P0: REDESIGN HasNonCallFrameTryCatchInHead — HIGHEST PRIORITY

Your analysis showed the problem: `HasNonCallFrameTryCatchInHead` checks ALL sub-expressions,
but non-eval-first positions can have tryCatch that doesn't affect evaluation order.

### Fix: Define HasNonCallFrameTryCatchInEvalFirst

Only check the eval-first path (the sub-expression that steps next):
```lean
/-- HasNonCallFrameTryCatchInHead restricted to eval-first positions only. -/
inductive HasNonCallFrameTryCatchInEvalFirst : Flat.Expr → Prop where
  | tryCatch_direct : catchParam ≠ "__call_frame_return__" →
      HasNonCallFrameTryCatchInEvalFirst (.tryCatch body catchParam catchBody finally_)
  | seq_left : HasNonCallFrameTryCatchInEvalFirst e →
      HasNonCallFrameTryCatchInEvalFirst (.seq e e2)
  | let_init : HasNonCallFrameTryCatchInEvalFirst e →
      HasNonCallFrameTryCatchInEvalFirst (.let_ name e body)
  -- ... only eval-first positions (NOT seq_right, let_body, etc.)
```

### Steps:
1. Define `HasNonCallFrameTryCatchInEvalFirst` in the appropriate file
2. Replace usage of `HasNonCallFrameTryCatchInHead` at L17568 with the new predicate
3. The key theorem `HasReturnInHead_Steps_steppable` should be TRUE with EvalFirst
   (since tryCatch in non-eval-first positions can't intercept the return error)
4. Re-prove the sorry at L17568 using the weaker predicate

**Expected: -1 sorry**

## P1: COMPOUND ERROR PROPAGATION INFRASTRUCTURE (if P0 done)

14 ANF sorries need compound Flat.step? error propagation. The break/continue compound cases
(L26360, L26431) are the closest to the existing throw infrastructure.

Check if HasBreakInHead / HasContinueInHead already have step_nonError analogues.
If not, and you have time, they follow the EXACT same pattern as HasThrowInHead_step_nonError.

## P2: L26140, L26141 — tryCatch catchParam + body_sim

L26140: `catchParam ≠ "__call_frame_return__"` — this could be proved if we add a
well-formedness assumption that source programs don't use `__call_frame_return__`.
Check if `noCallFrameReturn` can be threaded here differently.

L26141: `body_sim` inner simulation — needs anfConvert_step_star to be proved by strong induction.
This is a deep recursive dependency. SKIP unless you see a shortcut.

## DO NOT WORK ON:
- L11186-L11557 (labeled trivial mismatch — proof agent, BLOCKED)
- ClosureConvertCorrect.lean (jsspec)
- CCExprEquiv/CCStateAgree (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasNonCallFrameTryCatch redesign" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
