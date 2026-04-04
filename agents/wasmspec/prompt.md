# wasmspec — Close L9027/9028/9052/9053 (if compound + HasIfInHead)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## ⚠️ IDLE FOR 5 DAYS. GET TO WORK. ⚠️

## STATE

Your targets are 4 sorries in if_step_sim at L9027, L9028, L9052, L9053.

Code at L9027-9028 (true branch):
```lean
        | var _ | this | _ => sorry -- var/this/compound condition
      all_goals sorry -- compound HasIfInHead
```

Code at L9052-9053 (false branch, identical pattern):
```lean
        | var _ | this | _ => sorry -- var/this/compound condition
      all_goals sorry -- compound HasIfInHead
```

Context: We're inside `if_direct` case of `hasIfInHead`. The condition `c_flat` is being case-split. The `lit` case is already proved (L8992-9026 for true, L9037-9051 for false). The remaining cases are `var`, `this`, and compound (anything else).

## TASK 1: Close L9027 and L9052 — var/this/compound condition

### Understanding the goal

At L9027, after `| var _ | this | _ =>`, the goal should be:
- We have `c_flat = .var name` (or `.this` or compound)
- We need to show the Flat if-expression can step to match the ANF step
- The ANF step evaluated `evalTrivial env cond` where cond came from normalizeExpr

### Strategy for var case

When `c_flat = .var name`:
1. `Flat.step?` on `.if (.var name) then_ else_` will first step the condition: `.var name` → `.lit v` (via env lookup)
2. Then a second step evaluates `.if (.lit v) then_ else_` → branch
3. This is a 2-step simulation

Use `lean_goal` at L9027 to see exactly what's needed. The key insight: `normalizeExpr_if_lit_decomp` won't work here since the condition is `.var`, not `.lit`. You need a different decomposition lemma or need to construct the 2-step simulation manually.

### For the `_` (compound) case

This is harder — compound conditions may take many steps. Consider using `sorry` with a comment for now.

### Concrete approach

1. First use `lean_goal` at L9027 to understand the exact proof state
2. Try splitting into `var`/`this`/other:
```lean
        | var vname =>
          -- .var steps to .lit in one step, then .if (.lit v) steps to branch
          sorry -- 2-step: var→lit, then if→branch
        | this =>
          -- .this steps to .lit in one step, then .if (.lit v) steps to branch
          sorry -- 2-step: this→lit, then if→branch
        | _ => sorry -- compound condition: multi-step
```
3. Then try to close the var/this cases using explicit Flat.Steps construction

## TASK 2: Close L9028 and L9053 — compound HasIfInHead

These handle cases where `.if` is nested in a compound expression via `HasIfInHead`:
- `HasIfInHead.seq_left`, `.let_init`, `.assign_val`, etc.
- Each one means the .if is inside an evaluation context

For each case, the outer expression (e.g., `.seq (.if ...) b`) steps by stepping the inner `.if`. Use the IH from the outer induction.

1. Use `lean_goal` at L9028 to see the HasIfInHead cases
2. For each case, construct the step explicitly

## TASK 3 (IF TIME): Close L8856 (let_step_sim)

## COORDINATE WITH PROOF AGENT
- proof agent works on L9147-9168 (NoNestedAbrupt cases). DO NOT touch L9107-9170.
- You work on L9027-9053. These are DIFFERENT.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
