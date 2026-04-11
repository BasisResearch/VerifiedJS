# wasmspec — FINISH HasNonCallFrameTryCatchInHead for L15343

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T19:05
- Total: **49 real sorries** (ANF 37, CC 12). DOWN 11 from 15:30!
- proof agent closed 6 ANF sorries. Great momentum.
- YOUR TASK: Continue HasNonCallFrameTryCatchInHead to close L15343 (1 sorry).

## P0: HasTryCatchInHead branch at L15343 — 1 sorry

### Your plan from last run:
Define `HasNonCallFrameTryCatchInHead` (same as HasTryCatchInHead but `tryCatch_direct` requires `cp ≠ "__call_frame_return__"`). Key insight:
1. Non-call-frame tryCatches only come from source try/catch — never introduced by stepping
2. Call-frame tryCatches only from function calls
3. normalizeExpr `.return` implies no tryCatch in initial expression head
4. So intermediate states only have call-frame tryCatches

### Steps:
1. Define `HasNonCallFrameTryCatchInHead` inductive type
2. Prove `step_nonError_preserves_noNonCallFrameTryCatchInHead` — non-error steps don't introduce non-call-frame tryCatch
3. Use this to close the sorry at L15343

### Fallback:
If this approach is too large (>400 lines), consider:
- Proving only for the specific constructors needed (return head position)
- Or deferring and switching to return/yield .let compound (P2)

## P1: Compound throw (L13853) — 1 sorry
BLOCKED by HasThrowInHead_Steps_steppable (same infrastructure as P0). Only attempt after P0.

## P2: Return/yield .let compound (L19230, L19234, L19235) — 3 sorries
Also needs compound lifting infrastructure. Defer.

## P3: End-of-file (L22521, L22592) — 2 sorries
Defer.

## DO NOT WORK ON:
- L18644-L18650 (second-position + list — proof agent)
- L10843-L11214 (trivialChain zone — LSP timeout)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasNonCallFrameTryCatchInHead for P0" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
