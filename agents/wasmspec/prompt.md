# wasmspec — Close L9083/9084/9156/9157 (if compound + HasIfInHead)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATE — MAJOR PROGRESS ON NoNestedAbrupt

Proof agent + supervisor closed 23 of 30 NoNestedAbrupt cases. ANF sorry count dropped from 50 to 31. Your if compound targets are now at different line numbers due to edits. Use `grep -n "compound condition: multi-step\|compound HasIfInHead" VerifiedJS/Proofs/ANFConvertCorrect.lean` to find them.

## TASK 1: Close compound condition sorries (var/this cases)

Find the lines with `sorry -- compound condition: multi-step` (2 occurrences: true branch and false branch of normalizeExpr_if_step_sim).

For var/this cases when the condition is `.var name` or `.this`:
1. Flat.step? on `.if (.var name) then_ else_` first steps condition: `.var name` → `.lit v`
2. Then `.if (.lit v) then_ else_` → branch
3. This is a 2-step simulation

Split the sorry into explicit subcases:
```lean
        | var vname =>
          -- 2-step: var→lit, then if→branch
          sorry
        | this =>
          -- 2-step: this→lit, then if→branch
          sorry
        | _ => sorry -- compound condition: multi-step
```

Even splitting var/this out separately (still sorry) makes progress by narrowing what remains.

## TASK 2: Close compound HasIfInHead sorries

Find `all_goals sorry -- compound HasIfInHead` (2 occurrences).

These handle HasIfInHead cases where .if is nested in an evaluation context. Each case (seq_left, let_init, assign_val, etc.) steps the outer expression by stepping the inner .if.

Use `lean_goal` to see what cases remain and try to close them individually.

## TASK 3 (IF TIME): Close L8856 (let_step_sim)

## COORDINATE WITH PROOF AGENT
- proof agent works on L7791 (EndToEnd param addition) and hasAbruptCompletion_step_preserved
- DO NOT touch EndToEnd.lean or the hasAbruptCompletion theorem

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
