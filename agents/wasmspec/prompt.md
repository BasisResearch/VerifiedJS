# wasmspec — Close ANF step sim sorries: let, while, if compound

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.8GB available right now.
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: step?_preserves_funcs and Steps_preserves_funcs are PROVED (0 sorries in Flat/Semantics.lean). Focus entirely on ANF step sim sorries.

## CURRENT ANF SORRY MAP (26 sorries)

**Eval context / compound (14 sorries — PARKED, hard):**
- L7701, 7734, 7745, 7826, 7859, 7870, 7887: normalizeExpr_labeled_step_sim
- L8531, 8682, 8688, 8859, 8865, 9017, 9023: HasThrow/Return/Await/Yield compound

**Step sim (6 sorries — YOUR TARGETS):**
- L9050: let step sim
- L9140, 9152: while step sim (condition value + condition-steps)
- L9333, 9334: if compound condition + HasIfInHead (first if)
- L9406, 9407: if compound condition + HasIfInHead (second if)

**Other (6 sorries — proof agent targets):**
- L9451: tryCatch step sim (deferred)
- L9460: hasAbruptCompletion_step_preserved (proof agent)
- L9469: NoNestedAbrupt_step_preserved (proof agent)
- L9866, 9919: break/continue compound (proof agent)

## TASK 1: Close L9050 (let step sim) — HIGHEST PRIORITY

Use `lean_goal` at L9050 to see the exact state. The pattern:
- ANF has `.let name init body` with `exprValue? init = none`
- ANF.step? steps init to get sa'
- Need: find flat steps that simulate this

Check how normalizeExpr handles `.let`:
```bash
grep -n "| let_\|| .let" VerifiedJS/ANF/Normalize.lean | head -20
```

The normalization of `.let name init body k` should produce something like:
`normalizeExpr init (fun init_triv => .let name (trivialToExpr init_triv) (normalizeExpr body k))`

So when ANF steps init → init', the flat version should step the normalized init sub-expression. This follows the same eval-context simulation pattern used for seq/assign/binary/etc.

Use `lean_hover_info` on normalizeExpr at the let_ case to confirm the structure, then construct the flat step proof.

## TASK 2: Close L9333/9334 + L9406/9407 (if compound condition + HasIfInHead)

These are in the if step simulation. L9333/9406 handle compound (non-value, non-labeled) conditions. L9334/9407 handle HasIfInHead cases.

Use `lean_goal` at L9333 to understand what's needed. Pattern:
- ANF has `.if cond then_ else_` where cond is compound
- ANF.step? steps within cond
- Need: flat steps within normalizeExpr of the if

For HasIfInHead: this means the if itself is in head position of another if. The outer if's condition evaluated to the inner if. Check what HasIfInHead constructors exist:
```bash
grep -n "HasIfInHead" VerifiedJS/Proofs/ANFConvertCorrect.lean | head -20
```

## TASK 3: Close L9140/L9152 (while step sim) — IF TIME

These are harder:
- L9140: while condition value — transient state that doesn't match normalizeExpr directly
- L9152: condition stepping in while — needs multi-step flat simulation because while desugars to if+seq+while

For L9140, check if the value case can be handled by showing the flat while also reduces (condition is already a value → if-true/false branch).

For L9152, this may need a `while_condition_step_sim` helper that shows: if flat while condition steps, the normalized form also steps.

## PRIORITY ORDER
1. L9050 (let step sim) — most tractable
2. L9333/9334 + L9406/9407 (if compound) — medium difficulty
3. L9140/L9152 (while) — hardest, may need multi-step

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
