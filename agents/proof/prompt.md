# proof — Close if_step_sim (L6864/6867/6883), then tryCatch_step_sim (L6910)

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 24 sorry occurrences (grep -c). DOWN FROM 30 LAST RUN. GREAT PROGRESS — keep going.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` (L6785) entirely.

## YOUR IMMEDIATE TASK: Close if_step_sim sub-sorries

The remaining if_step_sim sorries are:
- **L6864**: toBoolean v = true → step to then_ branch
- **L6867**: toBoolean v = false → step to else_ branch
- **L6883**: normalizeExpr_if_cond_var_free (error case — var not bound)

### For L6864 and L6867 (true/false branches):
You need `normalizeExpr_if_source` — if `normalizeExpr e k` produces `.if cond then_ else_` with trivial-preserving `k`, then `e = .if fc ft fe`.

`bindComplex_not_if` ALREADY EXISTS (line ~469). Follow the SAME pattern as `normalizeExpr_seq_while_first_family` (lines ~767-1068).

```lean
private theorem normalizeExpr_if_source
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t' n', ∃ m', (k t').run n' = .ok (.trivial t', m'))
    (n m : Nat) (cond : ANF.Trivial) (then_ else_ : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (.if cond then_ else_, m)) :
    ∃ (fc : Flat.Expr) (ft fe : Flat.Expr),
      e = .if fc ft fe := by
  cases e with
  | «if» fc ft fe => exact ⟨fc, ft, fe, rfl⟩
  | lit v =>
    simp [ANF.normalizeExpr] at hnorm
    have ⟨m', hkm⟩ := hk (.litTrivial v) n
    rw [hkm] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  | var name' =>
    simp [ANF.normalizeExpr] at hnorm
    have ⟨m', hkm⟩ := hk (.var name') n
    rw [hkm] at hnorm; exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1
  -- For constructors using bindComplex: unfold normalizeExpr, use bindComplex_not_if
  -- For .seq, .while_: use normalizeExpr_seq_while_first to get contradiction
  -- For .let, .tryCatch, .labeled: unfold normalizeExpr, show they don't produce .if
  | _ => sorry -- Fill per-constructor
```

Once you have `normalizeExpr_if_source`, use it in L6864/6867:
```lean
have ⟨fc, ft, fe, he_if⟩ := normalizeExpr_if_source sf.expr k hk n m cond then_ else_ hnorm
subst he_if
-- Now sf.expr = .if fc ft fe, match flat semantics for .if
```

### For L6883 (var not bound):
Build `normalizeExpr_if_cond_var_free`: if normalizeExpr e k = .if (.var name) then_ else_ with trivial-preserving k, then either name is free in e, or name was introduced by normalizeExpr (in which case it's bound in sa_env). The key insight is that ANF normalization only introduces FRESH names (via `freshName`), and these are immediately bound in the .let that wraps them. So a `.var name` at the top-level condition of `.if` must come from the original expression.

### After if_step_sim: tryCatch_step_sim (L6910)
Same pattern: build `normalizeExpr_tryCatch_source` using `bindComplex_not_tryCatch` (line ~480).

## SKIP THESE:
- `let_step_sim` (L6785) — bindComplex PRODUCES .let, characterization WRONG
- `seq_step_sim` — blocked on SimRel while-loop generalization
- ClosureConvertCorrect.lean — other agents own it
- LowerCorrect.lean — DONE (0 sorries)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
