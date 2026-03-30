# proof — DELETE 40 aux-lemma sorries, then close expression cases

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell string)

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## STATE (22:05): 58 sorries, build PASSES

### Sorry breakdown:
- **40 hasBreak/hasContinue aux** (L3954-4030 + L4085-4161): ALL have same root cause
- **7 depth-induction** (L3825-3923): normalizeExpr_labeled_step_sim
- **2 makeEnv/objectLit/arrayLit** (L4036, L4167): inside aux lemmas
- **1 compound flat_arg** (L4336)
- **1 HasThrowInHead non-direct** (L4339)
- **7 expression-case** (L4370-4509): throw/return/await/yield/let/seq/if+tryCatch

## PRIORITY 1: DELETE aux lemmas → saves 42 sorries INSTANTLY

The 42 sorries in `hasBreakInHead_step?_error_aux` (L3927-4036) and
`hasContinueInHead_step?_error_aux` (L4058-4167) are **fundamentally unprovable**.
The conclusion `s'.expr = .lit .undefined` is WRONG for compound cases — step?
wraps sub-results in the parent context.

**DO THIS NOW:**

**Step 1**: Delete `hasBreakInHead_step?_error_aux` entirely (L3927-4036).
**Step 2**: Delete `hasContinueInHead_step?_error_aux` entirely (L4058-4167).

**Step 3**: Rewrite `hasBreakInHead_flat_error_steps` (L4041) to use STRUCTURAL
INDUCTION on `h : HasBreakInHead e label` with multi-step (Steps, not step?).
Drop the false `s'.expr = .lit .undefined` and env/heap preservation claims:

```lean
private theorem hasBreakInHead_flat_error_steps
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label)
    (sf : Flat.State) (hsf : sf.expr = e) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      observableTrace evs = observableTrace [.error ("break:" ++ label.getD "")] := by
  induction h generalizing sf with
  | break_direct =>
    subst hsf; exact ⟨_, [_], .tail ⟨by unfold Flat.step?; rfl⟩ (.refl _), rfl⟩
  | seq_left _ ih =>
    subst hsf; obtain ⟨sf', evs, hsteps, hobs⟩ := ih _ rfl
    exact ⟨sf', evs, Flat.Steps_seq_ctx hsteps, hobs⟩
  -- etc: each constructor lifts the inner Steps through a context lemma
```

Same for `hasContinueInHead_flat_error_steps`.

**Step 4**: Fix callers. Use `lean_goal` at each caller to see what the
weakened conclusion requires. The callers only need the observableTrace
equivalence — they never used the expr/env/heap claims.

**Step 5**: Build and verify. Target: 58 → 16 sorries.

## PRIORITY 2: Close 7 expression-case sorries (if time)

After aux deletion, these are at ~L4370-4509:
- `normalizeExpr_return_step_sim`
- `normalizeExpr_await_step_sim`
- `normalizeExpr_yield_step_sim`
- `normalizeExpr_let_step_sim`
- `normalizeExpr_seq_step_sim`
- `normalizeExpr_if_step_sim`
- `normalizeExpr_tryCatch_step_sim`

For each: `lean_goal` → `lean_multi_attempt` → follow the `.var` case pattern.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec own this
- Flat/Semantics.lean — jsspec modified this

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
