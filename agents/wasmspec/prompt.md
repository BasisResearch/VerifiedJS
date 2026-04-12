# wasmspec — HasNonCallFrameTryCatch REDESIGN + BREAK/CONTINUE INFRASTRUCTURE

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T05:05
- Total: **43 real sorries** (ANF 31, CC 12). Down from 63 (-20).
- noCallFrameReturn refactoring DONE.
- L17804 (HasNonCallFrameTryCatch) still BLOCKED — predicate too strong.

## P0: REDESIGN HasNonCallFrameTryCatchInHead — HIGHEST PRIORITY (-1 sorry)

The current `HasNonCallFrameTryCatchInHead` checks ALL sub-expressions including
non-eval-first positions. This is too strong — tryCatch in non-eval-first positions
(like the body of a seq_right, or let_body) doesn't affect evaluation order.

### Fix: Define HasNonCallFrameTryCatchInEvalFirst
Only check the eval-first path (the sub-expression that Flat.step? evaluates next):
```lean
inductive HasNonCallFrameTryCatchInEvalFirst : Flat.Expr → Prop where
  | tryCatch_direct : catchParam ≠ "__call_frame_return__" →
      HasNonCallFrameTryCatchInEvalFirst (.tryCatch body catchParam catchBody finally_)
  | seq_left : HasNonCallFrameTryCatchInEvalFirst e →
      HasNonCallFrameTryCatchInEvalFirst (.seq e e2)
  | let_init : HasNonCallFrameTryCatchInEvalFirst e →
      HasNonCallFrameTryCatchInEvalFirst (.let_ name e body)
  | binary_lhs : HasNonCallFrameTryCatchInEvalFirst e →
      HasNonCallFrameTryCatchInEvalFirst (.binary op e rhs)
  -- Add ONLY positions where Flat.step? recurses into the sub-expression
  -- Do NOT add: seq_right, let_body, if branches, tryCatch body/catch, etc.
```

### Steps:
1. Check where `HasNonCallFrameTryCatchInHead` is defined — `lean_local_search`
2. Define `HasNonCallFrameTryCatchInEvalFirst` nearby
3. Replace usage at L17804 with the new predicate
4. The key theorem should now be provable: eval-first tryCatch is the ONLY kind that
   can intercept the return error during stepping

**Expected: -1 sorry**

## P1: BREAK/CONTINUE COMPOUND INFRASTRUCTURE (if P0 done)

L26596 and L26667 need compound error propagation for break/continue cases.
Same pattern as HasThrowInHead — but for HasBreakInHead/HasContinueInHead.

Check if `HasBreakInHead_step_nonError` and `HasContinueInHead_step_nonError` exist.
If not, they follow the EXACT same pattern as HasThrowInHead_step_nonError.
This would close 2 sorries and establish infrastructure for more.

## P2: L26376 (catchParam ≠ "__call_frame_return__")

This needs `noCallFrameReturn` threaded as a precondition. Check if the caller of
the theorem at L26376 already has noCallFrameReturn in scope. If so, just thread it.

## DO NOT WORK ON:
- L11365-L11736 (labeled trivial mismatch — BLOCKED)
- ClosureConvertCorrect.lean (jsspec)
- CCExprEquiv/CCStateAgree (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasNonCallFrameTryCatch redesign" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
