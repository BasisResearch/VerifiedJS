# proof — Close L6883 (var_free lemma), then L6864/6867 (if branch sim)

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 24 sorry occurrences. Good progress on if_step_sim error case.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` (L6785) entirely.

## YOUR IMMEDIATE TASK: Close L6883 first, then L6864/6867

### TASK 1: Build `normalizeExpr_if_cond_var_free` (to close L6883)

You need a lemma analogous to `normalizeExpr_var_implies_free` (line ~1950).
That existing lemma proves: if normalizeExpr produces `.trivial (.var name)`, then `VarFreeIn name e`.

You need the SAME thing for the `.if` condition:
```lean
private theorem normalizeExpr_if_cond_var_free :
    ∀ (d : Nat) (e : Flat.Expr), e.depth ≤ d →
    ∀ (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n m : Nat)
      (name : ANF.VarName) (then_ else_ : ANF.Expr),
    (∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m')) →
    (ANF.normalizeExpr e k).run n = .ok (.if (.var name) then_ else_, m) →
    VarFreeIn name e := by
```

**Proof strategy** (follow `normalizeExpr_var_implies_free` at L1950 exactly):
1. Strong induction on `d` with cases on `e`
2. For each constructor, unfold `normalizeExpr` and analyze
3. Key insight: if output is `.if (.var name) ...` at top level, the `.var name` either:
   - Comes from `k` being trivial-preserving → but `k` produces `.trivial`, not `.if` → contradiction
   - Comes from bindComplex wrapping in `.let` → the `.if` is INSIDE `.let`, not at top level → contradiction
   - Comes from the original `.if` case where cond is already a var → `VarFreeIn name e` directly
   - Comes from `.seq a b` where the `.if` emerges from normalizing `b` → recurse with `VarFreeIn name b → VarFreeIn name (.seq a b)`

Once this lemma exists, close L6883:
```lean
| var name_cond =>
  simp only [ANF.evalTrivial] at herr
  split at herr
  · simp at herr
  · rename_i hnone
    have hfree := normalizeExpr_if_cond_var_free sf.expr.depth sf.expr (Nat.le_refl _)
      k n m name_cond then_ else_ hk_triv hnorm_simp
    have hbound := hewf name_cond hfree
    simp only [ANF.State.env] at henv
    rw [← henv] at hbound
    exact hbound hnone
```

### TASK 2: Strong induction for L6864/6867 (if branch simulation)

After L6883 is closed, tackle L6864 (true branch) and L6867 (false branch).

**Approach**: Strong induction on `sf.expr.depth`:
1. If `sf.expr = .if fc ft fe` where fc is trivial chain → direct: use `steps_if_var_branch`/`steps_if_lit_branch`
2. If `sf.expr = .seq a b` → normalizeExpr_seq_while_first says `a = .while_` → seq prefix steps, then recurse on smaller depth
3. Other constructors → `bindComplex_not_if` says bindComplex can't produce `.if` → contradiction with `hnorm`

### TASK 3: tryCatch_step_sim (L6910)
Same strong-induction approach with `bindComplex_not_tryCatch`.

## SKIP THESE:
- `let_step_sim` (L6785) — bindComplex PRODUCES .let, characterization WRONG
- `seq_step_sim` — blocked on SimRel while-loop generalization
- ClosureConvertCorrect.lean — other agents own it

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
