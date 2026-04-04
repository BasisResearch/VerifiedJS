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

## STATE — SUPERVISOR CLOSED setIndex

Supervisor just closed the setIndex case in NoNestedAbrupt_step_preserved. ANF sorry count is now 30 (was 31). Your if compound targets are still open.

Find current line numbers:
```
grep -n "compound condition: multi-step\|compound HasIfInHead" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

## TASK 1: Close compound condition sorries (remaining non-var/non-this cases)

These are the `| _ => sorry -- compound condition: multi-step` cases. The condition is a compound expression (seq, let, assign, call, etc.) — NOT var/this/lit.

For compound conditions:
1. The condition `c` is not a value, so `Flat.step?` on `.if c then_ else_` steps `c` first
2. After stepping c → c', we get `.if c' then_ else_`
3. This requires: show Flat takes 1+ steps on the if, matching the ANF step

Use `lean_goal` at the sorry to see exactly what's needed. The key lemma pattern:
```lean
        | _ =>
          -- c is compound: Flat.step? on .if c _ _ steps c via step?_if_cond_step
          have hc_not_val : Flat.exprValue? c = none := by cases c <;> simp [Flat.exprValue?] <;> contradiction
          sorry
```

If you can prove the compound case needs trivialChain infrastructure, document what's needed and move to Task 2.

## TASK 2: Close compound HasIfInHead sorries

Find `all_goals sorry -- compound HasIfInHead` (2 occurrences).

These handle HasIfInHead cases where .if is nested inside seq/let/assign/etc. Each HasIfInHead constructor (seq_left, let_init, assign_val, etc.) provides a sub-expression that IS an .if. The outer expression steps by stepping this inner sub-expression.

Pattern for each case:
```lean
    | seq_left hif =>
      -- sf.expr = .seq a b where a contains .if via HasIfInHead
      -- Flat.step? steps a, reducing the inner .if
      sorry
```

Use `lean_goal` on each case to see what's available.

## TASK 3 (IF TIME): Close L8856 (let_step_sim)

L8856: `sorry -- Need characterization of what produces .let, flat simulation`

## COORDINATE WITH PROOF AGENT
- proof agent works on L7791 (EndToEnd param addition), hasAbruptCompletion, and list helper lemmas
- DO NOT touch EndToEnd.lean or the hasAbruptCompletion theorem or firstNonValueExpr helpers

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
