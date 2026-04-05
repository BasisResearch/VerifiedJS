# wasmspec — Close if compound + while sorries in ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.8GB available right now.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9468 (tryCatch step sim) and L9067 (let compound)
- **YOU** work on L9350/9351 and L9423/9424 ONLY
- DO NOT touch lines 9060-9070 or 9440-9470

## STATUS: step? cleanup and if_step_sim errors fixed. Focus ONLY on if compound closures.

## YOUR TARGETS (4 sorries)

| Line | What | Difficulty |
|------|------|------------|
| L9350 | if compound condition (first if) — `| _ => sorry` | Medium |
| L9351 | HasIfInHead (first if) — `all_goals sorry` | Medium |
| L9423 | if compound condition (second if) — `| _ => sorry` | Medium |
| L9424 | HasIfInHead (second if) — `all_goals sorry` | Medium |

## TASK 1: Close L9350/9351 (first if compound)

Use `lean_goal` at L9350 to see the exact proof state.

The structure: `normalizeExpr_if_step_sim` handles `.if cond then_ else_` where the condition is compound (not a value, not labeled). ANF steps within the condition. Need to show Flat can step within the normalized condition.

Pattern:
- L9350 is `| _ => sorry -- compound condition: multi-step`. This is the case where `exprValue? cond = none` and `step? cond` gives us a stepped condition.
- The normalizeExpr of the if produces something like `.if (normalizeExpr cond ...) ...`
- Flat needs to step within the condition part, matching the ANF step.

For L9351 (HasIfInHead compound cases):
- These are cases where the if has a HasIfInHead constructor on a compound sub-expression
- Handle each compound constructor (seq_left, seq_right, let_init, etc.)
- Most should be exfalso (normalizeExpr can't produce these forms) or follow the same IH pattern

## TASK 2: Close L9423/9424 (second if compound)

Same pattern as Task 1 but for the second if case. Once you solve L9350/9351, copy-paste and adapt for L9423/9424.

## PRIORITY ORDER
1. L9350/9351 (first if compound) — solve the pattern
2. L9423/9424 (second if compound) — copy-paste solution

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
