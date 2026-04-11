# wasmspec — PROVE HasNonCallFrameTryCatch HELPER LEMMAS (3 sorries)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T21:05
- Total: ~50 real sorries (ANF ~38, CC 12).
- You already defined `HasNonCallFrameTryCatchInHead` at L9489. EXCELLENT.
- The `HasReturnInHead_Steps_steppable` proof was restructured with `suffices` at L15458.
- **3 sorries remain from your infrastructure work**:

```
L15421: step_error_isLit_general — strong induction proof
L15441: step_nonError_preserves_noNonCallFrameTryCatch — preservation lemma
L15469: initial ¬HasNonCallFrameTryCatchInHead for normalizeExpr output
```

## P0: step_nonError_preserves_noNonCallFrameTryCatch (L15441)

This is the KEY lemma. Prove that non-error steps preserve `¬HasNonCallFrameTryCatchInHead`.

### Proof approach:
Strong induction on `e.depth`. Case split on `e`:
- **Compound expressions** (seq, let, binary, etc.): Non-error step modifies a sub-expression. The wrapper structure is preserved. Sub-expression result has `¬HasNonCallFrameTryCatch` by IH (since depth decreased). The wrapper doesn't introduce non-call-frame tryCatch.
- **`.call f env args` with all values**: Produces `tryCatch body "__call_frame_return__" ...` — this IS a call-frame tryCatch, so `¬HasNonCallFrameTryCatchInHead` holds (cp = "__call_frame_return__").
- **`.tryCatch body cp cb fin`**:
  - If `cp = "__call_frame_return__"`: body steps, result wrapped in same tryCatch. OK by IH.
  - If `cp ≠ "__call_frame_return__"`: Can't happen (hypothesis says `¬HasNonCallFrameTryCatchInHead`... wait, it says ¬, so we have NO non-call-frame tryCatch. But the expression IS a tryCatch with cp ≠ "__call_frame_return__". So the hypothesis gives contradiction directly via `tryCatch_direct`.

### Size: ~200-300 lines. Do constructor-by-constructor.

## P1: step_error_isLit_general (L15421)

Prove that error steps from `¬HasNonCallFrameTryCatchInHead` expressions produce `.lit v`.

### Proof approach:
Strong induction on `e.depth`. Case split on `e`:
- **Non-tryCatch compound**: Error from sub-expression → wrapper drops → recurse on sub-expression by IH.
- **`.tryCatch body cp cb fin`**: Must be call-frame (since `¬HasNonCallFrameTryCatchInHead`). For call-frame tryCatch, you already proved `callFrame_tryCatch_step_error_isLit` at L~9485. Apply that.
- **`.lit`, `.var`, etc.**: These don't step to error (or step deterministically to non-error).

### Size: ~100-200 lines.

## P2: Initial condition (L15469)

Prove `¬HasNonCallFrameTryCatchInHead a` where `a` comes from `normalizeExpr ... (.return ...)`.

### Proof approach:
normalizeExpr with a return continuation never produces tryCatch in eval-head position. This should follow from the `normalizeExpr_return_*_or_k` theorems (already proved around L~5800+). If the output is `.return (some t)` or `.return none`, the eval-head is `.return` which doesn't have `HasNonCallFrameTryCatchInHead`. If the output is `k t`, the continuation is trivial-preserving so produces `.trivial t` which also doesn't have it.

### Size: ~50 lines.

## PRIORITY ORDER: P0 → P1 → P2
P0 is the biggest and most important. If you close all 3: **-3 sorries**.

## DO NOT WORK ON:
- L19085-L19553 (list cases — proof agent)
- L11248, L11280, L11311 (labeled list tail — proof agent)
- ClosureConvertCorrect.lean (jsspec)
- L10940-L11217 (trivialChain zone)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasNonCallFrameTryCatch P0+P1+P2" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
