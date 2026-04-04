# wasmspec — Close L8925/L8928 (if step sim) using HasIfInHead you just built

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## GREAT JOB building HasIfInHead infrastructure. Now USE it.

## STATE: ANF has 22 sorry lines. Your targets: L8925 + L8928.

## YOUR TASKS (in priority order)

### TASK 1: Close L8925 (if step sim, toBoolean = true → then_)

You built `normalizeExpr_if_or_k` and `normalizeExpr_if_implies_hasIfInHead`. Now use them.

At L8925, the goal is: given `ANF.step?` on `.if cond then_ else_` with `toBoolean v = true`, show Flat steps from sf to some sf' matching the then_ branch.

The proof pattern:
1. `normalizeExpr_if_implies_hasIfInHead` tells you sf.expr has `.if` at eval head position
2. Use `HasIfInHead` to identify the Flat `.if` form
3. Flat steps: evaluate condition to value, then step `.if (lit v) then_flat else_flat` to `then_flat` (since `toBoolean v = true`)
4. Establish ANF_SimRel for the resulting state with `then_` and `then_flat`

Use `lean_goal` at L8925 to see exact goal shape. Use `lean_multi_attempt` to test tactics.

Key pieces you'll need:
- `Flat.step?_if_true`: Flat steps `.if (lit v) then else` to `then` when `toBoolean v = true`
- `normalizeExpr_if_or_k`: your new disjunction theorem
- The normalizeExpr equation for `.if cond then_ else_`

### TASK 2: Close L8928 (if step sim, toBoolean = false → else_)

Same pattern as L8925 but with `toBoolean v = false` → `else_flat`.

### TASK 3: If blocked, try L8846 (let step sim)

L8846 needs characterization of what produces `.let` from normalizeExpr. You may need a `HasLetInHead` infrastructure similar to HasIfInHead. But try simpler approaches first — `lean_goal` at L8846 to see if the proof follows from existing normalizeExpr equations.

### TASK 4: If still blocked, try L8894 (while step sim)

L8894 is marked as needing multi-step simulation for while loops. Only attempt if T1-T3 are done or blocked.

### COORDINATE WITH PROOF AGENT
proof agent is working on L8204/L8339 (NoNestedAbrupt exfalso for throw) and L8489/8492 (return compound). DO NOT touch those areas. Your work on L8925/L8928 is separate and should not conflict.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
