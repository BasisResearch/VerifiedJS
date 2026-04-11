# wasmspec — COMPOUND INNER DEPTH SORRIES (6 closable)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- ANF: 40 sorries. CC: 15. Total: 55.
- ALL trivialChain sorries confirmed blocked. DO NOT WORK ON THOSE.
- hasAbruptCompletion_step_preserved being fixed by proof agent (errors at L13962).

## P0: L10759 — COMPOUND INNER DEPTH

This sorry is at line 10759 in ANFConvertCorrect.lean.

**Context**: The catch-all `| _ =>` at L10756 covers compound (non-labeled) inner_val inside `.return (some (.return (some inner_val)))`.

**The IH `ih` is available** (check with `lean_goal` at L10759):
```
ih : ∀ (e : Flat.Expr), e.depth ≤ d →
  ∀ (k n m label body), ... → normalizeExpr e k n = ok (labeled label body, m) →
  ∀ sf, sf.expr = e → ExprWellFormed e sf.env →
  ∃ evs sf', Steps sf evs sf' ∧ ...
```

**The goal** requires: given inner_val with HasLabeledInHead, find Steps from sf to some sf' where normalizeExpr sf'.expr produces the body.

**Proof strategy:**
1. Run `lean_goal` at L10759 to see exact hypotheses and goal
2. Extract `HasLabeledInHead inner_val label` from the surrounding `hlh` using `cases hlh`
3. Show `inner_val.depth ≤ d` from `hd` (the `.return (some (.return (some inner_val))).depth ≤ d + 1` bound): `simp [Flat.Expr.depth] at hd; omega`
4. Apply `ih inner_val hdepth ...` with appropriate k, n, sf arguments
5. Lift the resulting Steps through `.return (some (.return (some ·)))` using `Steps_return_some_ctx_b` (search: `lean_local_search "Steps_return_some_ctx_b"`)

**IMPORTANT**: The catch-all `| _ =>` has MANY sub-goals (one per non-labeled constructor: lit, var, seq, let, etc.). The proof may need `all_goals` or separate handling per constructor. Start with `lean_goal` to see exactly what's there.

After L10759, adapt for:
- L10795: inner_val inside `.return (some (.yield (some inner_val) delegate))` — use `Steps_return_some_ctx_b` + `Steps_yield_some_ctx_b`
- L10808: catch-all for yield variants
- L10891, L10926, L10939: yield outer layer variants

## SKIP: trivialChain (blocked), if_branch, while, tryCatch, error prop cases (proof agent owns those)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound inner depth L10759" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
