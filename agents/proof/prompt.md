# proof — COMPOUND ERROR PROPAGATION IS THE ONLY PATH

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T05:05
- ANF: **31** real sorries. CC: 12. Total: **43**.
- Down from 63 last run (-20). GREAT PROGRESS — infrastructure is paying off.
- HasThrowInHead infrastructure: DONE.
- 12 trivial-mismatch sorries (L11365-L11736): BLOCKED, no known fix. DO NOT TOUCH.

## ANF SORRY MAP (31 total):

**Blocked — DO NOT TOUCH (12):**
- L11365, L11413, L11461, L11511, L11538, L11588, L11590, L11640, L11642, L11673, L11705, L11736
  (labeled trivial mismatch — needs architectural rethink)

**P0: step_error_isLit (L14348) — 1 sorry, EASY WIN**
This is a standalone lemma. Prove by cases on `Flat.step?`. Every error-producing step
sets sf'.expr to a `.lit` value. The comment says "strong induction on sf.expr.depth" but
you can likely do it by just unfolding step? and checking each arm.

**P1: hasThrowInHead compound (L14386) — 1 sorry, HIGH LEVERAGE**
This is the catch-all for compound HasThrowInHead cases. You need:
1. A Steps lifting lemma: if sub-expr steps, the compound wrapping steps too
2. Error propagation: compound Flat.step? passes errors through
The direct/return/yield/await cases are already handled (lines 14376-14385).
Remaining: seq_left, seq_right, let_init, binary_lhs, etc.
Each compound case: get sub-expr HasThrowInHead from IH, show Flat steps through the wrapper.

**P2: Compound error propagation (7 sorries):**
- L23086 (HasAwaitInHead compound)
- L23259 (HasYieldInHead compound)
- L23315, L23319 (return/yield some val compound)
- L23320 (compound expressions catch-all)
- L23410, L23422 (while condition)
ALL share the same blocker: need Flat.step? error propagation for compound cases.
Once P0+P1 establish the pattern, these follow the same approach.

**P3: If-branch K-mismatch (2 sorries):**
- L24147 (if true), L24187 (if false)
- Collapsed for OOM. `lean_goal` to check current state.

**P4: TryCatch (3 sorries):**
- L25028, L25046, L25049
- Body error/step + compound. Deferred unless P0-P2 done.

**P5: End-of-file (4 sorries):**
- L26376 (catchParam ≠ "__call_frame_return__" — needs noCallFrameReturn assumption)
- L26377 (body_sim — needs strong induction)
- L26596, L26667 (break/continue compound — same pattern as P2)

**Wasmspec owns (1):**
- L17804 (HasNonCallFrameTryCatch — wasmspec working on it)

## EXECUTION ORDER: P0 → P1 → P2 → P3

P0 is easiest. Do it FIRST. Then P1 which unlocks P2 (7 sorries). If those go well,
try P3. That's potentially -11 sorries this cycle.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — P0 step_error_isLit + P1 compound throw" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
