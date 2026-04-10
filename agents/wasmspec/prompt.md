# wasmspec — While condition-steps + if_branch investigation

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~3.5GB free. USE LSP ONLY — no builds.

## CONCURRENCY
- proof agent works on Flat/Semantics.lean + compound sorries (L11550-12210)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own L12268-12372 (while) AND L13976-15525 (if_branch)

## STATUS: 67 sorries total. Your previous analysis found all 24 if_branch sorries blocked by K-mismatch. Good work on the analysis. Now try to close while sorries.

## ===== P0: WHILE CONDITION-STEPS (L12368) =====

Your own analysis identified this as "normalizeExpr-compatible form". This means it might be closable.

The comment says:
```
-- sa'.expr = .seq (.while_ sc.expr d) b — this IS a normalizeExpr-compatible form
-- Needs: decomposition of hnorm to extract the flat while condition,
-- recursive SimRel for condition stepping, and reconstruction.
```

### CONCRETE STEPS:
1. `lean_goal` at L12368 to see the exact proof state
2. You need to reconstruct a SimRel for the new state where:
   - ANF: `.seq (.while_ sc.expr d) b`
   - Flat: the corresponding flat state after stepping the while condition
3. Key: the `normalizeExpr_while_decomp` theorem (L12270) decomposes normalizeExpr(.while_ cond body) into condition + body + continuation normalizations
4. After the flat condition steps, the new flat condition expr is `sc.expr`
5. Need to show normalizeExpr(.while_ sc.expr body, k) produces an expression that matches the ANF `.while_ sc'.expr d'` state
6. Use `lean_local_search "while"` to find while-related infrastructure

### STRATEGY:
- The condition stepped from `cond` to `sc.expr` in both ANF and Flat
- The SimRel should be reconstructable because the normalizeExpr structure is preserved
- The key is showing that `normalizeExpr(cond, fun t => pure (.trivial t))` and the flat condition stepping are compatible

## ===== P1: WHILE CONDITION VALUE (L12356) — harder =====

The comment says "transient state breaks single-step SimRel". The ANF state after while unrolls is:
- `.seq (.seq d (.while_ c d)) b` (if condition true) or `.seq (.trivial .litUndefined) b` (if false)

These transient forms aren't directly normalizeExpr-compatible. You'd need multi-step simulation.

Try L12368 first. If that works, attempt L12356.

## ===== P2: IF_BRANCH K-MISMATCH INVESTIGATION =====

Only if P0/P1 are done or stuck.

Your K-mismatch analysis was thorough. The question is: can the theorem `normalizeExpr_if_branch_step` be redesigned to avoid requiring exact `then_`/`else_` matching?

Investigate: What does the CALLER of `normalizeExpr_if_branch_step` actually need? If the caller only needs the observable trace to match, maybe the theorem can be weakened.

Search: `lean_local_search "if_branch_step"` to find callers.

## WORKFLOW
1. Start with `lean_goal` at L12368
2. Search for while-related infrastructure
3. Try to close L12368
4. If stuck, try L12356
5. Log your work

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
