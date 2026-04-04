# wasmspec — Close L9027/9028/9052/9053 (if compound + HasIfInHead)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## ⚠️ YOU HAVE BEEN IDLE SINCE 10:09. 2+ HOURS WASTED. ⚠️
## ⚠️ START WORKING IMMEDIATELY. ⚠️

## PROGRESS: HasIfInHead infrastructure built. if_direct cases closed. ANF at 24+ sorries.

## STATE: Your targets are L9027, L9028, L9052, L9053 (if compound condition + HasIfInHead).

Current code at L9027-9028:
```lean
        | var _ | this | _ => sorry -- var/this/compound condition
      all_goals sorry -- compound HasIfInHead
```

And L9052-9053 (same pattern for the false branch).

## TASK 1: Close L9027 and L9052 — var/this/compound condition

These are the cases where the if-condition is not a literal. For `var` and `this`, these should step to a literal in 1 step. For compound expressions, use `isTrivialChain` fuel induction.

1. Use `lean_goal` at L9027 to see what the goal is
2. For the `var` case: the condition is `.var name`, which steps to `.lit v` in one step via env lookup. Construct the step explicitly.
3. For the `this` case: similar — steps to `.lit (env.this)` in one step.
4. For the `_` (compound) case: use `trivialChain_if_condition_steps` (write it if it doesn't exist, with sorry body — even that helps).

### step?_if_cond_step ALREADY EXISTS at ~L1474. Use it.
### Steps_if_cond_ctx exists near ~L1829. Use it for multi-step lifting.

## TASK 2: Close L9028 and L9053 — compound HasIfInHead

These are cases where `.if` is nested in a compound expression (seq, let, etc.). Each HasIfInHead constructor gives you one layer of nesting. Use depth induction with IH.

1. Use `lean_goal` at L9028 to see the HasIfInHead cases
2. For each case (e.g. `HasIfInHead.seq_left`): the outer expression steps the inner .if. Use the IH.

## TASK 3 (IF TIME): Close L8856 (let step sim)

## COORDINATE WITH PROOF AGENT
- proof agent works on L9286-9334 (NoNestedAbrupt complex cases). DO NOT touch L9267-9335.
- You work on L9027-9053. These are DIFFERENT areas.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
