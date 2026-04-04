# wasmspec — Close L9186/9187/9259/9260 (if compound + HasIfInHead)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATE UPDATE

Current ANF sorry count: 35. Your 4 targets:
- L9187: `| _ => sorry -- compound condition: multi-step`
- L9188: `all_goals sorry -- compound HasIfInHead`
- L9260: `| _ => sorry -- compound condition: multi-step`
- L9261: `all_goals sorry -- compound HasIfInHead`

## TASK 1: Close compound condition sorries (L9187, L9260)

Use `lean_goal` at L9187 to see the exact goal. The condition `c` is a compound expression (not var/this/lit). For compound conditions:
1. The condition `c` is not a value, so `Flat.step?` on `.if c then_ else_` steps `c` first
2. After stepping c → c', we get `.if c' then_ else_`

If you can prove it needs trivialChain infrastructure (multi-step simulation), document what's needed precisely and move to Task 2.

## TASK 2: Close compound HasIfInHead sorries (L9188, L9261)

Use `lean_goal` at L9188 to see all the HasIfInHead sub-goals. Each HasIfInHead constructor (seq_left, let_init, assign_val, etc.) says the `.if` is nested inside a compound expression. For each:
1. The outer expression steps by stepping the inner sub-expression containing `.if`
2. Show the flat step matches

Pattern: for each HasIfInHead constructor, unfold step? for the outer expression and show the inner `.if` step propagates.

## TASK 3 (IF TIME): Close L8960 (let_step_sim)

L8960: `sorry -- Need characterization of what produces .let, flat simulation`

## COORDINATE WITH PROOF AGENT
- proof agent works on hasAbruptCompletion call/newObj/makeEnv/arrayLit/objectLit/tryCatch cases and corresponding NoNestedAbrupt cases
- DO NOT touch the hasAbruptCompletion or NoNestedAbrupt theorems

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
