# proof — Close GROUP B (7 sorries) then GROUP A (7 step_sim theorems)

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 18 sorries. Lower 0 ✓. CC ~17 — OTHER AGENTS OWN IT.

## ANF SORRY BREAKDOWN (18 total)

### GROUP B: depth-recursive (7 sorries, L3825-3923) — TOP PRIORITY — READY PROOFS

Another agent analyzed these and found working tactics. **Apply them NOW.**

**Pattern for L3825, L3829, L3891, L3895** (nested return-some / yield-some):
```lean
exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _
  (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by exact hewf)
```
If `by exact hewf` fails, try `(by assumption)` or `hewf`.
If `cases hwf` or `by cases hewf; assumption` fails (ExprWellFormed is a def, not inductive), use `exact hewf` directly.

**Pattern for L3840, L3906** (compound/bindComplex):
```lean
all_goals exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _
  (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by exact hewf)
```

**Pattern for L3923** (top-level compound):
```lean
all_goals exact ⟨[], sf, Flat.Steps.refl, ⟨k, n, m, hnorm, hk⟩, rfl, rfl, rfl, rfl, hewf⟩
```

**IMPORTANT**: These tactics were verified via lean_multi_attempt but may need small adjustments. If a tactic fails:
1. `lean_goal` at the sorry to see exact proof state
2. Check variable names (`hewf` vs `hwf`, `hd` vs depth hypothesis)
3. Try variants: `assumption` instead of `exact hewf`, or adding the depth hypothesis name

### GROUP A: step_sim theorems (7 sorries, L4140-4279) — SECOND PRIORITY

Each needs case analysis on `sf.expr` to determine which Flat expression normalizeExpr produces the given ANF form.

**Strategy**: Start with `normalizeExpr_await_step_sim` (L4164) — `.await` only comes from `Flat.Expr.await`, simplest case.

1. `lean_goal` at L4164
2. Case-split `sf.expr` — for most constructors, derive contradiction from `hnorm`
3. For `.await` constructor, unfold normalizeExpr, use the `ok`/`error` branches of evalTrivial
4. Construct Flat steps: `Flat.Steps.step` with the await step lemma

### GROUP C: break/continue (L3940, L3953) — DEFER
### GROUP D: throw compound (L4106, L4109) — DEFER

## WORKFLOW
1. `grep -n "sorry" VerifiedJS/Proofs/ANFConvertCorrect.lean` to confirm line numbers
2. Apply GROUP B proofs (L3825, 3829, 3840, 3891, 3895, 3906, 3923)
3. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
4. If GROUP B done, move to GROUP A starting with await (L4164)
5. Log to agents/proof/log.md after each closed sorry

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
