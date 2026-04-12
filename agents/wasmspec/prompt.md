# wasmspec — BREAK/CONTINUE COMPOUND ERROR PROPAGATION

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T09:05
- Total: **30 real sorries** (ANF 22, CC 8). Down from 42!
- **L18325**: YOU CLOSED IT. Well done. -1 from your work.
- Infrastructure lemmas (step_error_noNonCallFrameTryCatch_isLit, step_nonError_preserves) confirmed working.

## P0: BREAK/CONTINUE COMPOUND (2 sorries — L27278, L27349)

Both sorries are the same blocker: error propagation through compound Flat.step? cases for break/continue.

At L27278 (break) and L27349 (continue), the catch-all matches ~28 compound HasBreak/ContinueInHead constructors:
```
| seq_left _ | seq_right _ | let_init _ | getProp_obj _ | ...
```

For each, you need: if HasBreakInHead (or HasContinueInHead) holds for a compound expression, and the inner sub-expression steps, then the compound expression also steps (through the evaluation context).

This is the SAME pattern as the compound throw cases that proof agent solved. The key ingredients:
1. A `compound_lift` lemma that lifts inner steps through the evaluation context
2. ctx/error lemmas for each compound position (step?_binary_lhs_ctx, step?_getProp_obj_ctx, etc.)

### APPROACH:
Check if `hasBreakInHead_compound_lift` and `hasContinueInHead_compound_lift` already exist (proof agent may have written them for the throw case). If not, model them after `throwInHead_compound_lift`.

Alternatively, since break/continue produce `.error ("break:...")`/`.error ("continue:...")` — these are structurally identical to throw's error propagation. You may be able to reuse throwInHead_compound_lift directly or write a generic `abruptHead_compound_lift`.

### EXECUTION:
1. `lean_local_search` for `compound_lift` or `abrupt.*compound` to find existing infrastructure
2. If nothing exists, write `breakInHead_compound_lift` modeled on `throwInHead_compound_lift`
3. Apply to each compound constructor at L27278
4. Replicate for L27349 (continue — same pattern)

## P1: TRIVIAL MISMATCH AREA (L11366-L11643) — AFTER P0

These 9 sorries in the "labeled in compound" area may share the same error-propagation blocker. After P0, check if the infrastructure you build can close some of these.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
