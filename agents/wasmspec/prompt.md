# wasmspec — Close trivialChain + let/if step sim sorries in ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## YOUR TASKS (in priority order)

### TASK 1: Close L7711 (trivialChain seq case normalizeExpr passthrough)

The proof agent started the trivialChain_throw_steps proof and got stuck at L7711 in the `.seq a b` case. The issue: after stepping `.seq a b` to `e'`, we need to show `normalizeExpr e' k = normalizeExpr b k` (i.e., normalizeExpr is a "passthrough" for trivial chains that discards the left side of seq).

Read the context around L7700-7712 carefully with `lean_goal` at L7711. You likely need a helper lemma:
```lean
private theorem normalizeExpr_trivialChain_seq_passthrough
    (a b : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n : Nat)
    (htc : isTrivialChain (.seq a b) = true) :
    (ANF.normalizeExpr (.seq a b) k).run n = (ANF.normalizeExpr b k).run n := by
  simp [ANF.normalizeExpr]  -- normalizeExpr of seq recurses on a, then b
  sorry -- may need induction on a if non-trivial
```

Or the approach might be simpler: `normalizeExpr (.seq a b) k` = `do let _ ← normalizeExpr a (fun _ => pure (.trivial _)); normalizeExpr b k`. For trivial `a`, normalizeExpr a just returns a trivial, so the seq becomes `normalizeExpr b k`.

Use `lean_hover_info` on `ANF.normalizeExpr` and `lean_goal` at L7711 to understand the exact goal.

### TASK 2: Close L7762 (TRIVIAL_CHAIN_IN_THROW)

After L7711 is closed, the trivialChain proof at L7762 should become provable. The `¬HasThrowInHead e` + `isTrivialChain e = true` branch needs to show `.throw e` steps to a terminal state matching `ANF.evalTrivial env arg`.

### TASK 3: If blocked on T1/T2, work on L8398 (let step sim) or L8477/L8480 (if step sim)

These are independent sorries that don't need NoNestedAbrupt or trivialChain. Use `lean_goal` to understand what's needed.

### COORDINATE WITH PROOF AGENT
proof agent is working on NoNestedAbrupt exfalso closures (L7756, L8044, L8217, L8371). DO NOT touch those areas. Your work on L7711/L7762 is below their work and should not conflict. If you see merge conflicts, check the area proof agent is editing and work around it.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
