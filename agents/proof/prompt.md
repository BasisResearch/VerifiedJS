# proof — COMPOUND THROW + ERROR PROPAGATION

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T07:30
- ANF: **30** real sorries. CC: 12. Total: **42**.
- Unchanged since 06:05 (-0). step_error_isLit PROVED. Infrastructure solid.
- 12 trivial-mismatch sorries (L11366-L11737): BLOCKED, DO NOT TOUCH.
- L18355 (HasNonCallFrameTryCatch): wasmspec CONFIRMED EvalFirst approach DEAD. DO NOT TOUCH.

## ANF SORRY MAP (30 total):

**Blocked — DO NOT TOUCH (13):**
- L11366, L11414, L11462, L11512, L11539, L11589, L11591, L11641, L11643, L11674, L11706, L11737
  (labeled trivial mismatch — needs architectural rethink)
- L18355 (HasNonCallFrameTryCatch — wasmspec working on noCallFrameReturn approach)

**P0: compound throw catch-all (L14937) — 1 sorry, HIGH LEVERAGE**
This is `| _ => sorry` remaining compound cases: second-operand and list-based.
You have `throwInHead_compound_lift` working for first-operand cases (seq_left, let_init,
binary_lhs, call_func, newObj_func all PROVED). Now handle:
- `binary_rhs`: second operand — need step?_binary_rhs_ctx/error
- `call_args`: list-based — need normalizeExprList handling
- `newObj_args`: list-based — same pattern
- `objectLit_value`, `arrayLit_element`, etc.

For list-based: the tricky part is that normalizeExprList/normalizeProps produce
lists. You may need a list-based version of throwInHead_compound_lift.
If this is too complex for one run, split `| _ =>` into individual cases and sorry each.
15 individual sorries is BETTER THAN 1 opaque catch-all.

**P1: Compound error propagation (5 sorries):**
- L23641 (HasAwaitInHead compound)
- L23814 (HasYieldInHead compound)
- L23870, L23874 (return/yield some val)
- L23875 (compound catch-all)

These ALL need the same infrastructure as P0 but for await/yield/return compound cases.
Once P0 pattern is established, apply it here.

**P2: While condition (2 sorries):**
- L23965, L23977 (while condition stepping)

**P3: If-branch K-mismatch (2 sorries):**
- L24702 (if true), L24742 (if false)

**P4: TryCatch (3 sorries):**
- L25583, L25601, L25604

**P5: End-of-file (4 sorries):**
- L26931 (catchParam), L26932 (body_sim), L27151, L27222

## EXECUTION ORDER: P0 → P1 → P2

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
