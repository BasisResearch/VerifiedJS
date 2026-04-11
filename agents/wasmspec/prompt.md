# wasmspec — PIVOT: CLOSABLE ANF SORRIES (not trivialChain)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- ANF: 41 sorries. CC: 17. Total: 58.
- Error propagation done in Flat/Semantics.lean.
- **YOU CONFIRMED**: ALL trivialChain passthrough sorries (L10183-L10408) are blocked by trivial mismatch (`.var x ≠ trivialOfFlatValue v`). DO NOT WORK ON THESE.

## WHAT'S BLOCKED (skip all of these):
- L10183, L10231, L10279, L10329, L10356, L10406 — trivial mismatch (confirmed)
- L10408, L10460 — list decomposition (same root cause)
- L13057, L13097 — if_branch K-mismatch
- L13938, L13956, L13959 — tryCatch callStack
- L12320, L12332 — while transient state

## P0: INFRASTRUCTURE — trivialOfFlatValue reconciliation lemma

The trivial mismatch blocks ~10 sorries. Instead of working on individual sorries, create the INFRASTRUCTURE to fix them all:

The problem: `normalizeExpr` produces `.var x` as the trivial for a sub-expression, but flat evaluation gives `trivialOfFlatValue v` (which is `.lit v`). We need a lemma that reconciles these.

Key insight: Under `ExprWellFormed`, if `normalizeExpr e k` succeeds and produces trivial `t`, and flat evaluation steps `e` to value `v`, then `t` and `trivialOfFlatValue v` are "equivalent" in that using either in `k` produces the same result (because the flat semantics binds `v` to the variable named by `t`).

1. `lean_local_search "normalizeExpr_trivialChain"` — understand current infrastructure
2. `lean_local_search "trivialOfFlatValue"` — see definition
3. `lean_local_search "ExprWellFormed"` — understand well-formedness
4. `lean_hover_info` on `normalizeExpr_trivialChain_apply` at L1466

**Possible lemma:**
```lean
theorem normalizeExpr_trivial_value_equiv
    (e : Flat.Expr) (v : Core.Value) (t : ANF.Trivial)
    (heval : Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs ⟨.lit (.value v), ...⟩)
    (hnorm : normalizeExpr e k = .ok (body_t, m))
    (hnorm_v : normalizeExpr e k' = .ok (body_v, m'))
    -- t comes from normalizeExpr, trivialOfFlatValue v comes from evaluation
    -- The bodies using either are equivalent
    : ...
```

Or alternatively, prove that for trivialChain expressions, normalizeExpr gives `.lit v` not `.var x`:
```lean
theorem normalizeExpr_trivialChain_is_lit
    (htc : trivialChain e)
    (heval : Flat.Steps ... ⟨.lit (.value v), ...⟩)
    : normalizeExpr e k = normalizeExpr_with_lit v k
```

Check what's actually needed by reading the goal at one of the blocked sorries (e.g., L10183).

## P1: COMPOUND INNER DEPTH CASES (L10759-L10939, 6 sorries)

These are in `normalizeExpr_labeled_branch_step` — depth induction for compound inner expressions inside return/yield wrappers. The IH should apply (inner depth ≤ d-1).

1. `lean_goal` at L10759
2. Check if IH is available and what it needs
3. `lean_multi_attempt` with relevant tactics

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — trivial reconciliation infrastructure" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
