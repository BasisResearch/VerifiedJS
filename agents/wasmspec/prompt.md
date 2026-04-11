# wasmspec — CONTINUE LABELED_BRANCH + LIST DECOMPOSITION

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- BUILD PASSES. 0 errors.
- You closed 3 sorries previously (L9865, L10220, L10550). GREAT WORK.
- Supervisor deleted 4 dead-code sorries. ANF: 41. CC: 15. Total: 56.
- Line numbers shifted ~90 lines up due to dead code deletion around L2967-L3140.

## P0: CLOSE REMAINING TYPE (a) LABELED_BRANCH CASES

Target sorries (line numbers may have shifted ~90 lines up from previous prompt):
- L10233, L10281, L10331, L10358, L10408, L10460 — same pattern as L10372 (newObj_func) you already closed

Use `grep -n "sorry" VerifiedJS/Proofs/ANFConvertCorrect.lean | head -20` to find current line numbers.

Template from your previous proof:
1. Get IH from HasLabeledInHead hypothesis
2. Use `Steps_*_ctx_b` lifting lemma to lift inner steps through compound context
3. Provide normalizeExpr witness

For each:
1. `lean_goal` to see exact goal
2. Check which `Steps_*_ctx_b` lemma exists with `lean_local_search "Steps_" "ctx_b"`
3. Apply the template

## P1: LIST DECOMPOSITION (call_args, newObj_args, makeEnv, objectLit, arrayLit) — IF P0 DONE

These need stepping through list elements:
- `lean_local_search "Steps_" "list"` or `"ctx"` to check for list lifting lemmas
- If no list lifting infrastructure exists, document what's needed and skip

## P2: DEPTH INDUCTION (L10761, L10797, L10810, L10893, L10928, L10941) — ASSESS ONLY

These are compound inner expressions inside return/yield wrappers. `lean_goal` at each to understand structure.

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — labeled_branch continuation" >> agents/wasmspec/log.md`
2. Find current sorry line numbers after dead code deletion
3. Close as many type (a) cases as possible using template
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
