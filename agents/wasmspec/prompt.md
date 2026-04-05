# wasmspec — Close let/while/tryCatch ANF step sim sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.8GB available right now.
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: Good work fixing 4 if_step_sim simp errors! if_step_sim section now clean.

## TASK 1: Prove Flat.step?_preserves_funcs (NEW — shared with proof agent)

Both proof agent and you need this lemma. If it doesn't exist yet in Flat/Semantics.lean, add it:

```lean
theorem step?_preserves_funcs (sf : Flat.State) (ev : Core.TraceEvent) (sf' : Flat.State)
    (h : step? sf = some (ev, sf')) : sf'.funcs = sf.funcs := by
  -- Unfold step? and inspect every branch
  unfold step? at h
  -- Each branch constructs sf' with the same funcs
  split at h <;> simp_all [pushTrace]
```

This should be straightforward — step? never modifies funcs. Check with `lean_hover_info` on step? to verify.

## TASK 2: Close L9050 (let step sim)

```lean
sorry -- Need characterization of what produces .let, flat simulation
```

This is the case where ANF has a `.let name init body` and `exprValue? init = none`, so ANF.step? steps `init`. The normalizeExpr for `.let` should produce a Flat `.let` with normalized init and body.

**Approach:**
1. `lean_goal` at L9050 to see the exact proof state
2. `lean_hover_info` on `ANF.normalizeExpr` for the `.let` case
3. The key: if `normalizeExpr (.let name init body) k` produces a Flat let, then stepping init in ANF corresponds to stepping the normalized init in Flat

You likely need:
- `normalizeExpr_let_decomp`: shows normalizeExpr of .let decomposes into normalizeExpr of init + body
- Then connect ANF.step? on `.let` with Flat.step? on the normalized form

## TASK 3: Continue while sub-cases (L9140, L9152)

You already split L9093 and added `normalizeExpr_while_decomp`.

- **L9140**: while condition value case. The transient `.seq (.seq d (.while_ c d)) b` form is NOT directly normalizeExpr-compatible. This may need multi-step simulation (Flat takes multiple steps to match one ANF step).

- **L9152**: condition-steps case. Flat `.while_ c d` desugars to `.if c (.seq d (.while_ c d)) (.lit .undefined)`. When ANF steps the condition, Flat needs to:
  1. Desugar while → if (one silent step)
  2. Step the condition inside the if

This requires a 2-step Flat simulation. Check if `Flat.Steps` can handle this.

## TASK 4: L9451 (tryCatch step sim) — IF TIME

```lean
sorry
```

Similar pattern: ANF has .tryCatch, need to show Flat simulation matches.

## PRIORITY ORDER
1. `step?_preserves_funcs` — quick lemma, unblocks proof agent too
2. L9050 (let) — most tractable
3. L9140, L9152 (while) — harder, needs multi-step
4. L9451 (tryCatch) — if time

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
