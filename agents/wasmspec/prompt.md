# wasmspec — CLOSE LABELED_BRANCH SIMPLE CASES + CAT B

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- BUILD PASSES. 0 errors.
- You closed 3 sorries last run (L9865, L10220, L10550). GREAT WORK — keep that momentum.
- ANF: 48 sorries. CC: 15. Total: 63.
- Your categorization of labeled_branch sorries was excellent.

## P0: CLOSE TYPE (a) LABELED_BRANCH CASES (L10383, L10431, L10481, L10508, L10558)

These follow the SAME PATTERN as L10550 (newObj_func) which you already closed. Template:
1. Get IH from HasLabeledInHead hypothesis
2. Use `Steps_*_ctx_b` lifting lemma to lift the inner steps through the compound context
3. Provide normalizeExpr witness

For each:
1. `lean_goal` to see exact goal
2. Check which `Steps_*_ctx_b` lemma exists with `lean_local_search "Steps_" "ctx_b"`
3. Apply the template from L10550

### Priority order:
- L10383 (binary_lhs) — most similar to your closed cases
- L10431 (binary_rhs) — same pattern, different argument
- L10481 (unary) — single argument variant
- L10508 (call_func) — compound with env+args context
- L10558 (call_env) — similar to call_func

## P1: LIST DECOMPOSITION CASES (L10560, L10612, L10643, L10675, L10706) — IF P0 DONE

These need stepping through list elements. Try `lean_local_search "Steps_" "list"` or `"ctx"` to see if list lifting lemmas exist. If not, document what's needed and skip.

## P2: CAT B BREAK/CONTINUE (L15316, L15327, L15546, L15617) — ASSESS ONLY

Check if error propagation changes make these closable now. Use `lean_goal` at each. If closable, close them. If still blocked, document the exact blocker.

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — labeled_branch type (a)" >> agents/wasmspec/log.md`
2. Close L10383, L10431, L10481, L10508, L10558 using L10550 template
3. Assess P1 and P2
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
