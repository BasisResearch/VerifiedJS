# wasmspec — Close L9045 (let step sim) and L9093 (while/seq step sim)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.1GB available right now.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: ANF has 11 sorries. Proof agent is working on equation lemmas + L9398/L9677. You focus on the step-sim sorries.

## YOUR TARGETS

### TARGET 1: L9045 (normalizeExpr_let_step_sim)

This is the `let` step simulation sorry. Use `lean_goal` at L9045 to see the exact goal state.

The key insight: `normalizeExpr` on a `.let name init body` produces either:
- Direct `.let` when init is trivial
- A bindComplex form when init is complex

ANF.step? on `.let` either evaluates init (if value) or steps init. We need to show Flat can match this.

Approach:
1. Use `lean_goal` at L9045
2. Check what `hnorm` gives us about the Flat expression structure
3. The Flat `.let` case of `step?` (Flat/Semantics.lean L348-358) either substitutes (value init) or steps init
4. Try: `obtain ⟨...⟩ := normalizeExpr_let_decomp ...` if such a lemma exists
5. Use `lean_local_search` for "normalizeExpr_let" to find available lemmas

### TARGET 2: L9093 (seq/while step sim)

The comment says: "When exprValue? c = none and step? c = some (t, sc): sa_inner.expr = .while_ sc.expr d, giving sa'.expr = .seq (.while_ sc.expr d) b — this IS handleable."

So the sub-case where the while condition steps (not evaluates to a value) should be closeable. Approach:
1. `lean_goal` at L9093
2. Split on `exprValue? c` in the inner while step
3. The case where c is a value creates transient `.seq (.seq d (.while_ c d)) b` which breaks SimRel (this case may need sorry)
4. The case where c steps to sc gives `.seq (.while_ sc.expr d) b` which preserves SimRel

Even closing ONE sub-case of L9093 and leaving a sorry on the other is progress.

### TARGET 3 (if 1-2 blocked): L10375/L10428 (break/continue compound)

These need: when break/continue is nested in a compound expression (call, seq, etc.), Flat.step? steps the outer expression. This requires showing that compound expressions with break/continue inside must step (since they're not values).

## DO NOT just analyze. WRITE CODE. Close at least 1 sorry line.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
