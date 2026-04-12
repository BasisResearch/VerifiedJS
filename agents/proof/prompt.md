# proof — COMPOUND THROW + ERROR PROPAGATION

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T06:05
- ANF: **30** real sorries. CC: 12. Total: **42**.
- Down from 43 last run (-1). step_error_isLit FULLY PROVED. Infrastructure solid.
- 12 trivial-mismatch sorries (L11366-L11737): BLOCKED, DO NOT TOUCH.

## ANF SORRY MAP (30 total):

**Blocked — DO NOT TOUCH (12):**
- L11366, L11414, L11462, L11512, L11539, L11589, L11591, L11641, L11643, L11674, L11706, L11737
  (labeled trivial mismatch — needs architectural rethink)

**P0: compound throw catch-all (L14682) — 1 sorry, HIGH LEVERAGE**
This is `| _ => sorry` in the HasThrowInHead compound cases. You have:
- ✅ `step_error_isLit` (PROVED)
- ✅ `HasThrowInHead_Steps_steppable` (PROVED)
- ✅ `HasThrowInHead_step_nonError` (PROVED, all 18 cases)

For each compound constructor (seq_left, seq_right, let_init, binary_lhs, etc.):
1. Get HasThrowInHead on the sub-expression from the IH
2. Use HasThrowInHead_Steps_steppable to show HasThrowInHead is preserved across Steps
3. Show the compound wrapper Flat.step? preserves the throw path

Do this by CASE SPLIT on the `| _ =>` catch-all. Each compound constructor case is
similar. Start with `seq_left` as a template, then do the rest.

**P1: Compound error propagation (7 sorries):**
- L23381 (HasAwaitInHead compound)
- L23554 (HasYieldInHead compound)
- L23610, L23614 (return/yield some val)
- L23615 (compound catch-all)
- L23705, L23717 (while condition)

These ALL need the same pattern as P0 but for different abrupt completion kinds.
Once P0 establishes the template, copy the approach.

**P2: If-branch K-mismatch (2 sorries):**
- L24442 (if true), L24482 (if false)
- Collapsed for OOM. `lean_goal` to check current state.

**P3: TryCatch (3 sorries):**
- L25323, L25341, L25344

**P4: End-of-file (4 sorries):**
- L26671 (catchParam), L26672 (body_sim), L26891, L26962

**Wasmspec owns (1):**
- L18100 (HasNonCallFrameTryCatch — wasmspec working on EvalFirst redesign)

## EXECUTION ORDER: P0 → P1 → P2

P0 is the highest leverage. If you prove L14682, the same pattern unlocks P1 (7 sorries).
That's potentially -8 sorries this cycle.

## CONCRETE APPROACH FOR P0 (L14682):

```lean
-- Replace the | _ => sorry with case analysis:
| seq_left h =>
  -- h : HasThrowInHead left
  -- normalizeExpr (.seq left right) k = normalizeExpr left (fun t => k (.seq t right_flat))
  -- Get Steps for left from IH, then show .seq wrapper steps too
  sorry
| let_init h =>
  sorry
| binary_lhs h =>
  sorry
-- ... etc for each HasThrowInHead constructor
```

Each case: use the IH to get Flat Steps for the sub-expression, then show the compound
expression takes matching steps through the wrapper.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — P0 compound throw L14682" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
