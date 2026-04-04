# wasmspec — Close L9045 (let) and L9100/9123 (while) + inner compound sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.1GB available right now.
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: 26 ANF sorry lines. Proof agent is working on equation lemmas + hasAbruptCompletion/NoNestedAbrupt. You focus on step-sim sorries.

## TARGET 1: Inner compound sorries L8677, L8854, L9012

These are `| _ => sorry` wildcards inside throw_step_sim, return_step_sim, await_step_sim where `inner_val` is a compound expression. With the `hna : NoNestedAbrupt sf.expr` parameter now available:

Approach for L8677 (inside normalizeExpr_throw_step_sim):
1. `lean_goal` at L8677 to see the goal
2. The inner_val is compound with `hasAbruptCompletion inner_val = false` (from NoNestedAbrupt)
3. Use `normalizeExpr_throw_or_k` to get: HasThrowInHead inner_val ∨ continuation case
4. HasThrowInHead inner_val → contradiction with hna
5. Continuation case → inner_val is trivial chain → use `trivialChain_throw_steps` (~170 lines, analog of existing throw version)

If full proof is too large, at minimum prove: HasThrowInHead case → exfalso. Leave trivial chain sorry.

## TARGET 2: L9045 (normalizeExpr_let_step_sim)

Use `lean_goal` at L9045. The let step simulation sorry.

Key: `normalizeExpr` on `.let name init body` either:
- Produces `.let name (normalizeExpr init id) (normalizeExpr body k)` when init is trivial
- Produces `bindComplex` form when init is complex

For the Flat step: `step?` on `.let name init body`:
- If `exprValue? init = some v`: substitution step → one flat step
- If `exprValue? init = none`: step init → one flat step

Use `lean_local_search` for "normalizeExpr_let" to find decomposition lemmas.

## TARGET 3: L9100/L9123 (while step sim)

L9100: "While condition value case: transient state breaks single-step SimRel"
L9123: "Condition-steps case: needs flat while-condition simulation"

For L9123 (condition steps):
- When `exprValue? c = none` and `step? c = some (t, sc)`: the while condition steps
- After step: `sa'.expr = .while_ sc.expr d` — this preserves SimRel
- This sub-case should be closeable

For L9100 (condition is value):
- Creates transient `.seq (.seq d (.while_ c d)) b` — may need sorry (multi-step)

Even closing L9123 alone is progress.

## DO NOT just analyze. WRITE CODE. Close at least 1 sorry line.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
