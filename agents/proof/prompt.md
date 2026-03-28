# proof — CLOSE HELPER SORRIES THEN STRUCTURAL CASES

## STATUS: 15 ANF sorries (was 13). Net +2 because normalizeExpr_labeled_step_sim added 3 sorries. FIX THIS.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## BUILD STATUS: PASSES (sorry warnings only). DO NOT BREAK IT.

## STEP 0: CLOSE THE 3 HELPER SORRIES IN normalizeExpr_labeled_step_sim (HIGHEST PRIORITY)

These are at L1148, L1154, L1171. They are ALL `exfalso` cases — proving normalizeExpr of certain constructors can't produce `.labeled`. The pattern is ALREADY PROVEN for while_ (L1155-1159) and tryCatch (L1160-1170) right above them. Copy that pattern:

### L1148: `return (some _)` case
```lean
    | some v =>
      exfalso; unfold ANF.normalizeExpr at hnorm
      simp only [StateT.run, bind, Bind.bind, StateT.bind, Except.bind] at hnorm
      repeat (first | split at hnorm | (simp [pure, Pure.pure, StateT.pure, Except.pure] at hnorm; try exact ANF.Expr.noConfusion (Prod.mk.inj (Except.ok.inj hnorm)).1))
```

### L1154: `yield (some _)` case — same pattern as return some

### L1171: `| _ => sorry` — remaining compound cases (let, seq, if, await, throw)
For each remaining constructor that hits this wildcard, the same exfalso + unfold + simp + split pattern should work. Replace the wildcard with explicit cases:
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

Use `lean_multi_attempt` on each case first to verify the tactic works before editing. If `repeat (first | split ... )` times out, try `set_option maxHeartbeats 400000` before the theorem.

## STEP 1: CLOSE seq CASE IN anfConvert_step_star (L1244)

After the helper sorries are gone (-3), tackle `seq` (L1244-1245). Pattern:
- ANF.step? for `.seq a b`: if `step? {s with expr := a}` succeeds → inner step, else if a is value → skip to b
- From hnorm: `normalizeExpr (.seq a b) k` = `normalizeExpr a (fun _ => normalizeExpr b k)`
- The inner a step case: use IH (recursion on depth) with the continuation modified
- The skip case: a is value → `normalizeExpr a k'` produces `.trivial`, then evaluate b

Use `lean_goal` at L1245 to see exact goal. The seq case is most mechanical of the structural cases.

## STEP 2: CLOSE if CASE (L1247)

ANF.step? for `.if cond then_ else_`: evaluates cond trivial, branches.
- From hnorm: `normalizeExpr (.if cond then_ else_) k` = `normalizeExpr cond (fun cv => ...)`
- Need to show Flat steps: evaluate cond to value, then take branch

## CASES TO SKIP: break (L1283), continue (L1285), return (L1255), throw (L1251) — SEMANTIC MISMATCH, LEAVE AS SORRY

## WORKFLOW
1. `lean_goal` at the sorry line
2. `lean_multi_attempt` with tactic candidates
3. Edit the sorry with working tactic
4. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
5. Move to next

## TARGET: Close 3 helper sorries (-3) + seq (-1) + if (-1) = net -5 this run

## Log progress to agents/proof/log.md
