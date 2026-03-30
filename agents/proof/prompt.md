# proof — ANF compound sub-cases. DO NOT TOUCH CC.

## ABSOLUTE RULE: YOU MAY ONLY EDIT ANFConvertCorrect.lean THIS RUN
- **DO NOT** open, read, build, or edit ClosureConvertCorrect.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (12:05 Mar 30)
- ANF: 81 sorries (decomposed — this is GOOD)
- Break/continue direct cases DONE ✓
- 66 compound sub-cases (33 break + 33 continue) are the bulk
- 15 other sorries (recursive depth, let/seq/if, throw, try-catch, return, yield, await)

## YOUR TASK: Close compound sub-cases that already have Fix D support

### CONTEXT: Fix D error propagation
Fix D exists for `.seq` and `.let` in Flat/Semantics.lean. When a sub-expression errors, the compound expression propagates the error and produces `.lit .undefined`.

jsspec is EXTENDING Fix D to all other compound expressions. But you can already close the seq/let cases NOW.

### Step 1: Close seq_left and seq_right for break (L3901-3902)

These compound sub-cases at L3901 (`| seq_left h => sorry`) and L3902 (`| seq_right h => sorry`) follow this pattern:

```lean
    | seq_left h =>
      -- h : HasBreakInHead a label, sf.expr = .seq a b
      -- IH: from HasBreakInHead induction, inner sub-expr `a` can step
      -- seq steps: Flat.step?_seq_ctx lifts the step through .seq
      -- When inner step is error: Fix D propagates → .lit .undefined
      -- Use existing step?_seq_sub_step and Flat_step?_seq_error lemmas
      sorry -- CLOSE THIS
```

The KEY lemmas you need are already in the file:
- `step?_seq_sub_step` (grep for it ~L1050-1060): lifts a sub-step through seq
- `Flat_step?_seq_error` (grep for it ~L1895): seq error propagation from Fix D

Write a helper theorem `break_compound_seq_left` that:
1. Takes `HasBreakInHead a label` for `.seq a b`
2. Uses IH to get Flat.Steps from `a` producing the break error
3. Lifts each step through `.seq` using step?_seq_sub_step
4. The final error step triggers Fix D (Flat_step?_seq_error)
5. Returns the Flat.Steps for `.seq a b` producing break error

Then apply it to both break and continue seq_left cases.

### Step 2: Close let_init for break (L3903) and continue (L3973)

Same pattern but for `.let name init body`. Use `Flat_step?_let_error` lemma.

### Step 3: If seq/let cases close, try the recursive depth sorries (L3631-3729)

These 7 sorries need induction on depth. Check if `sf.expr.depth` gives you a decreasing measure. Try:
```lean
    | some _ =>
      have : inner_expr.depth < sf.expr.depth := by simp [Flat.Expr.depth]
      exact ih inner_expr (by omega) ...
```

### Step 4: Do NOT attempt other compound sub-cases yet
Wait for jsspec to extend Fix D to getProp/setProp/binary/unary/etc. Those cases will follow the exact same pattern as seq once Fix D is there.

## VERIFICATION
- [ ] Edit ONLY ANFConvertCorrect.lean
- [ ] Build passes: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- [ ] Log to agents/proof/log.md with sorry count before/after
