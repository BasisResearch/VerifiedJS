# wasmspec — CONTINUE LABELED_BRANCH + CAT B ASSESSMENT

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- BUILD PASSES. 0 errors.
- You closed 3 sorries (L9865, L10220, L10550) and Cat A break/continue. GREAT WORK.
- ANF: 45 sorries. CC: 15. Total: 60.
- Your 22:30 run may still be in progress — if so, continue where you left off.

## P0: CLOSE REMAINING TYPE (a) LABELED_BRANCH CASES

Target sorries in labeled_branch area (L10361-L10734):
- L10411, L10459, L10509, L10536, L10586 — same pattern as L10550 (newObj_func) you already closed
- L10638 — similar pattern

Template from your L10550 proof:
1. Get IH from HasLabeledInHead hypothesis
2. Use `Steps_*_ctx_b` lifting lemma to lift inner steps through compound context
3. Provide normalizeExpr witness

For each:
1. `lean_goal` to see exact goal
2. Check which `Steps_*_ctx_b` lemma exists with `lean_local_search "Steps_" "ctx_b"`
3. Apply the L10550 template

## P1: LIST DECOMPOSITION (L10588, L10640, L10671, L10703, L10734) — IF P0 DONE

These need stepping through list elements (call_args, newObj_args, makeEnv, objectLit, arrayLit).
- `lean_local_search "Steps_" "list"` or `"ctx"` to check for list lifting lemmas
- If no list lifting infrastructure exists, document what's needed and skip

## P2: DEPTH INDUCTION (L10939, L10975, L10988, L11071, L11106, L11119) — ASSESS ONLY

These are compound inner expressions inside return/yield wrappers. `lean_goal` at each to understand structure.

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — labeled_branch continuation" >> agents/wasmspec/log.md`
2. Close as many type (a) cases as possible using L10550 template
3. If P0 done, assess P1/P2
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
