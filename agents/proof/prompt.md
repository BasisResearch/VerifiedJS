# proof — Close anfConvert_step_star expression cases + prove helper theorems

## ABSOLUTE RULE: YOU MAY ONLY EDIT ANFConvertCorrect.lean THIS RUN
- **DO NOT** open, read, build, or edit ClosureConvertCorrect.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (13:05 Mar 30)
- ANF: 17 sorries (down from 81! compound break/continue sub-cases ALL closed ✓)
- Break/continue compound sub-cases: ALL 66 proved via hasBreakInHead/ContinueInHead_flat_error_steps ✓
- Those 2 helper theorems (L3746, L3762) are sorry'd — they're USED 33× each
- 7 depth-induction sorries inside yield/return cases
- 8 expression-case sorries in anfConvert_step_star main body

## YOUR PRIORITY ORDER

### Priority 1: Expression cases in anfConvert_step_star (L3842-3874)

These are the CORE of the proof. Each is an independent case. Do them in order of difficulty:

#### 1a. `seq` (L3844) — EASIEST
Pattern: `sf.expr = .seq a b`. Two sub-cases:
- If `a` is a value: Flat.step? produces `.silent`, expr becomes `b`. ANF's normalizeExpr on `.seq a b` with value `a` gives `normalizeExpr b k`. Use seq_value lemma.
- If `a` is not a value: Flat.step? steps `a` to `a'`. ANF step depends on normalizeExpr inversion. Use `step?_seq_sub_step` (~L1050).

You have `Flat_step?_seq_error` for error propagation. `seq` already has Fix D.

#### 1b. `let` (L3842) — SIMILAR TO SEQ
Pattern: `sf.expr = .let name rhs body`.
- If `rhs` is value: Flat evaluates value, extends env, continues with body
- If `rhs` not value: step rhs. Use `Flat_step?_let_step` equivalent.

`.let` already has Fix D too.

#### 1c. `if` (L3846) — EVALUATE COND, BRANCH
Pattern: `sf.expr = .if cond then_ else_`. `cond` should be trivial after ANF.
- ANF.step? evaluates trivial `cond`, branches
- Flat.step? evaluates cond to value, branches
- Key: normalizeExpr of `.if cond then_ else_` gives structure you can invert

#### 1d. `return` (L3870), `yield` (L3872), `await` (L3874) — TRIVIAL ARG
These evaluate an optional trivial argument. After ANF, the argument should be `.trivial t`.
- `return none`: immediate, one Flat step
- `return (some arg)`: evalTrivial gives value, one Flat step

#### 1e. `throw` (L3866) — PARTIALLY DONE
The throw case at L3855-3866 already does `cases heval : ANF.evalTrivial sa_env arg`. Both cases produce `all_goals sorry`. The structure is there, just need to construct Flat steps for each sub-case.

#### 1f. `tryCatch` (L3868) — HARDEST, DO LAST
This needs multi-step reasoning about body execution, error catching, and finally.

### Priority 2: hasBreakInHead_flat_error_steps (L3746) and continue (L3762)

These helpers are sorry'd but used by all compound sub-cases. They need structural induction on HasBreakInHead.

**KEY INSIGHT**: For `break_direct`: trivial (already proved inline at L3912).
For compound cases like `seq_left h`: need multi-step Flat reasoning:
1. IH gives Flat.Steps from sub-expr to `.lit .undefined` with break error
2. Lift steps through compound expr via context stepping (e.g., step?_seq_sub_step)
3. Final error step triggers Fix D (for seq/let which have it)

**PROBLEM**: Non-seq/let cases (unary, binary, etc.) DON'T have Fix D yet. So for now:
- Prove the `break_direct`, `seq_left`, `seq_right`, `let_init` cases
- Leave other cases sorry'd with a comment "needs Fix D extension"
- This gives partial progress now, full closure after Fix D

### Priority 3: Depth induction sorries (L3631-3729)

These 7 sorries are inside yield/return/compound cases where normalizeExpr is called recursively. They need induction on expression depth. Try:
```lean
| some arg =>
  have hdepth : arg.depth < sf.expr.depth := by simp [Flat.Expr.depth]
  -- use structural recursion or well-founded on depth
```

## VERIFICATION
- [ ] Edit ONLY ANFConvertCorrect.lean
- [ ] Build passes: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- [ ] Log to agents/proof/log.md with sorry count before/after
