# proof — Close L6978 IMMEDIATELY (1 line), then L6959/6962

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` (L6835) entirely.

## STATE: ANF 24 sorries. normalizeExpr_if_cond_var_free ALREADY PROVED at L2026.

## YOUR IMMEDIATE TASKS (in order):

### TASK 1: Close L6978 — THE LEMMA ALREADY EXISTS (1 line fix!)
**This is a 1-line fix.** `normalizeExpr_if_cond_var_free` is ALREADY PROVED at line 2026.

At line 6978, replace:
```lean
        sorry -- Needs normalizeExpr_if_cond_var_free: if normalizeExpr e k = .if (.var name) ...
              -- with trivial-preserving k, then VarFreeIn name e
```
With:
```lean
        exact (hewf name_cond (normalizeExpr_if_cond_var_free sf.expr.depth sf.expr (Nat.le_refl _) k n m name_cond then_ else_ hk hnorm)) hnone
```

If `hewf` is not directly in scope (the function signature has it as parameter), check the hypothesis names with `lean_goal` at L6978. The logic is:
1. `normalizeExpr_if_cond_var_free` gives `VarFreeIn name_cond sf.expr`
2. `hewf` (ExprWellFormed) gives `sf.env.lookup name_cond ≠ none`
3. Contradiction with `hnone` (which says `sf.env.lookup name_cond = none`)

**DO THIS FIRST. Build and verify. This is -1 sorry with zero risk.**

### TASK 2: Close L6959 and L6962 (if branch true/false)

These are the true-branch (L6959) and false-branch (L6962) sorries in `normalizeExpr_if_step_sim`.

**Approach**: Strong induction on `sf.expr.depth` with case split:
1. `sf.expr = .if fc ft fe` (direct if): normalizeExpr produces .if directly from the condition. Use `steps_if_var_branch`/`steps_if_lit_branch` to show Flat takes the same branch. SimRel for the resulting then_/else_ sub-expression.
2. `sf.expr = .seq a b` where `a = .while_ c d`: normalizeExpr_seq_while_first says this is the only seq form, but .seq produces .seq not .if → contradiction.
3. Other constructors (.var, .lit, .this, .break, .continue, .return, .yield, .labeled, etc.): k produces .trivial not .if → contradiction via hk.

The key insight: with trivial-preserving k, normalizeExpr can only produce .if from:
- A direct `.if` expression
- `.return (some (.if ...))` / `.labeled _ (.if ...)` patterns that propagate .if through normalizeExpr

Use `normalizeExpr_if_cond_source` (should be near L2026) to determine which case applies.

### TASK 3: "non-labeled inner value" sorries (L5956, L5989, L6081, L6114)
Try `lean_multi_attempt` on each. These may close with contradiction tactics since they're in "impossible" branches.

### SKIP THESE:
- `let_step_sim` (L6880) — bindComplex PRODUCES .let, characterization WRONG
- `seq_step_sim` L6928 — blocked on SimRel while-loop generalization
- ClosureConvertCorrect.lean — other agents own it

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
