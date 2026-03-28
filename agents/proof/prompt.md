# proof — CLOSE HELPER SORRIES THEN STRUCTURAL CASES

## STATUS: 16 ANF sorries (was 15). Helper grew from 3→4 sorries because return-some/labeled case added ExprWellFormed sorry. FIX THIS.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## BUILD STATUS: PASSES (sorry warnings only). DO NOT BREAK IT.

## STEP 0: CLOSE THE 4 HELPER SORRIES IN normalizeExpr_labeled_step_sim (HIGHEST PRIORITY)

### L1180: ExprWellFormed sorry (return-some/labeled sub-case)
After `rw [hexpr_s]`, goal is `ExprWellFormed (.return (some b_flat)) s'.env`.
`b_flat` is a sub-expression of the original well-formed expression. Try:
```lean
    · rw [hexpr_s]
      intro x hfx; cases hfx with
      | return_some hinner => exact hewf _ (ExprFreeIn.return_some hinner)
```
If `ExprFreeIn` doesn't have a `return_some` constructor, check what constructors it has with `lean_hover_info` on `ExprFreeIn`. Alternative:
```lean
    · rw [hexpr_s]; exact hewf.return_some
```
Use `lean_goal` at L1180 and `lean_multi_attempt` to find working tactic.

### L1181: `| _ => sorry` — non-labeled val in return-some
For val ≠ labeled, normalizeExpr (.return (some val)) k can't produce .labeled.
The val cases to handle: var, lit*, this, let, seq, if, while_, tryCatch, throw, return, yield, await, break, continue.
For simple cases (var, lit*, this, break, continue): `exfalso; simp [ANF.normalizeExpr, ...] at hnorm`
For compound cases: same exfalso + unfold + split pattern as while_ (L1188-1192).

### L1187: yield-some — same structure as return-some
Copy the return-some pattern: cases on the inner expression, labeled sub-case steps, others are exfalso.

### L1204: `| _ => sorry` — remaining compound cases (let, seq, if, throw, await)
These ALL produce non-.labeled output. Replace wildcard with explicit cases:
```lean
  | «let» name rhs body =>
    exfalso; unfold ANF.normalizeExpr at hnorm
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
    repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
  | seq a b =>
    exfalso; unfold ANF.normalizeExpr at hnorm
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
    repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
  | «if» cond then_ else_ =>
    exfalso; unfold ANF.normalizeExpr at hnorm
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
    repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
  | throw arg =>
    exfalso; unfold ANF.normalizeExpr at hnorm
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
    repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
  | await arg =>
    exfalso; unfold ANF.normalizeExpr at hnorm
    simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
    repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
```
If `repeat` times out, add `set_option maxHeartbeats 400000` before the theorem.

## STEP 1: AFTER HELPERS ARE DONE, tackle seq (L1277) in anfConvert_step_star

Use `lean_goal` at L1277 to see exact goal. Pattern:
- ANF.step? for `.seq a b`: if a steps → inner step; if a is value → skip to b
- From hnorm: `normalizeExpr (.seq a b) k` = `normalizeExpr a (fun _ => normalizeExpr b k)`
- Use the var-found case (L1229-1265) as a template for constructing the simulation witness

## STEP 2: if case (L1279) — similar pattern to seq but with branching

## CASES TO SKIP: break (L1315), continue (L1317) — SEMANTIC MISMATCH, LEAVE AS SORRY

## WORKFLOW
1. `lean_goal` at the sorry line
2. `lean_multi_attempt` with tactic candidates
3. Edit the sorry with working tactic
4. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
5. Move to next

## TARGET: Close 4 helper sorries (-4) + seq (-1) = net -5 this run

## Log progress to agents/proof/log.md
