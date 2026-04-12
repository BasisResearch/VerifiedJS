# wasmspec — CLOSE noCallFrameReturn + HasNonCallFrameTryCatch SORRIES

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T02:05
- Total: **63 real sorries** (ANF 48, CC 15). UP FROM 42. CRISIS.
- Bridge lemma `noCallFrameReturn_normalizeExpr_tryCatch_param` is PROVED.
- `HasReturnInHead_Steps_steppable_core` is sorry-free.
- L17182 wrapper sorry is isolated.

## P0: noCallFrameReturn PRESERVATION (L26895 — 1 sorry)

Goal: `noCallFrameReturn sf2.expr = true` where sf2 comes from flat steps simulating one ANF step.

### Approach: prove noCallFrameReturn_step_preserved
```lean
theorem noCallFrameReturn_step_preserved
    (hncfr : noCallFrameReturn sf.expr = true)
    (hstep : Flat.step? sf = some (t, sf')) :
    noCallFrameReturn sf'.expr = true
```

Key insight: Flat.step? only introduces `__call_frame_return__` tryCatch for function calls (`.call`), and it wraps the ENTIRE call. After the call returns, the tryCatch is consumed and the result is a value (`.lit`). So:
- Non-call steps: preserve noCallFrameReturn structurally
- Call steps: the post-call expr is `.lit v` which trivially has noCallFrameReturn

Then extend to multi-step: `noCallFrameReturn_steps_preserved` for `Flat.Steps`.

At L26895, apply `noCallFrameReturn_steps_preserved hncfr hfsteps1`.

**Expected: -1 sorry**

## P1: HasNonCallFrameTryCatchInHead (L17182 — 1 sorry)

Goal: `¬HasNonCallFrameTryCatchInHead a` where `a` has `HasReturnInHead a`.

### Approach: thread through the caller chain
1. `HasReturnInHead_Steps_steppable` calls `HasReturnInHead_Steps_steppable_core` which needs `hncf`
2. The caller of `HasReturnInHead_Steps_steppable` is `hasReturnInHead_return_steps` or similar
3. Trace upward until you find where the expression comes from `normalizeExpr`
4. Prove: `normalizeExpr_no_nonCallFrameTryCatch_in_head` — normalizeExpr output never has non-call-frame tryCatch in head position (because normalizeExpr only creates .let, .seq, .labeled, .tryCatch with call-frame param)
5. Thread this property down to L17182

### Alternative (faster):
At the caller of `HasReturnInHead_Steps_steppable`, add `¬HasNonCallFrameTryCatchInHead` as precondition and prove it at the call site from normalizeExpr properties.

**Expected: -1 sorry**

## P2: L25975, L26046 — check what's needed
`lean_goal` at these lines. They may be closeable with existing infrastructure.

**Expected: -0 to -2 sorries**

## DO NOT WORK ON:
- L11186-L11557 (labeled trivial mismatch — proof agent, BLOCKED)
- ClosureConvertCorrect.lean (jsspec)
- Any CC file
- L14919-14936 (proof agent HasThrowInHead infrastructure)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — noCallFrameReturn + HasNonCallFrameTryCatch" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
