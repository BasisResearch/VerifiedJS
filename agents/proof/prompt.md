# proof — DELETE unprovable aux lemmas + close expression-case sorries

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell string)

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CRITICAL: hasBreakInHead_step?_error_aux is UNPROVABLE — DELETE IT

The 40 sorries at L3954-4030 and L4085-4161 are in `hasBreakInHead_step?_error_aux` and
`hasContinueInHead_step?_error_aux`. These theorems are **fundamentally wrong** and CANNOT
be proved. Here's why:

The theorem claims: for `.seq a b` where `HasBreakInHead a label`, a SINGLE `Flat.step?`
produces `s'.expr = .lit .undefined`. But `step?_seq_error` (L1216) shows that `step?`
on `.seq a b` when inner step errors gives `s'.expr = .seq sa.expr b`, NOT `.lit .undefined`.
The wrapper is preserved. This is confirmed by the raw `Flat.step?` definition (Flat/Semantics.lean L382-392).

### PRIORITY 1: Restructure break/continue error handling

**Step 1**: Delete `hasBreakInHead_step?_error_aux` (L3927-4038) entirely.
**Step 2**: Delete `hasContinueInHead_step?_error_aux` (L4058-4166) entirely.
**Step 3**: Rewrite `hasBreakInHead_flat_error_steps` (L4041) to use STRUCTURAL INDUCTION
on `h : HasBreakInHead e label` instead of delegating to the aux lemma.

The multi-step proof for each HasBreakInHead constructor:
- `break_direct`: Single step. `step? (.break label) = (.error "break:...", {expr := .lit .undefined})`. Done.
- `seq_left hsub`: By IH on `hsub`, get `Steps` from `{expr := a}` to `{expr := .lit .undefined}`.
  Need to LIFT these steps through `.seq _ b` context. Use `step?_seq_ctx` for non-error steps,
  `step?_seq_error` for the error step. After all IH steps: `expr = .seq (.lit .undefined) b`.
  Then ONE MORE step: `.seq (.lit .undefined) b` → `b` (seq-value rule). But then `expr = b ≠ .lit .undefined`.

  **THIS MEANS** the conclusion `sf'.expr = .lit .undefined` is WRONG for nested cases.

**Step 4**: You MUST weaken the conclusion. Change `hasBreakInHead_flat_error_steps` to:

```lean
private theorem hasBreakInHead_flat_error_steps
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label)
    (sf : Flat.State) (hsf : sf.expr = e)
    (hewf : ExprWellFormed e sf.env) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.funcs = sf.funcs ∧ sf'.callStack = sf.callStack ∧
      sf'.trace = sf.trace ++ evs ∧
      observableTrace evs = observableTrace [.error ("break:" ++ label.getD "")]
```

Drop the `sf'.expr = .lit .undefined` conclusion. The important thing is the error event is emitted.

**Step 5**: Fix ALL callers (around L4852-4900+). They currently use `hexpr'` (which was
`sf'.expr = .lit .undefined`). Search for `hasBreakInHead_flat_error_steps` and
`hasContinueInHead_flat_error_steps` usages and update them. The callers need `hexpr'` to
normalize expressions — without it, they need a different approach. Use `lean_goal` at each
call site to see what the weakened version gives you and how to proceed.

Same treatment for `hasContinueInHead_flat_error_steps`.

This will ELIMINATE 40 unprovable sorries (the aux lemmas) at the cost of introducing
proof obligations at call sites. But the call site obligations are PROVABLE.

### PRIORITY 2: Close expression-case theorems (if time remains)

These are independent of Priority 1:
- L4370: `normalizeExpr_return_step_sim` — `.return (some arg)` evaluation
- L4394: `normalizeExpr_await_step_sim` — `.await arg` evaluation
- L4425: `normalizeExpr_yield_step_sim` — `.yield (some arg)` evaluation
- L4446: `normalizeExpr_let_step_sim` — `.let name init body`
- L4467: `normalizeExpr_seq_step_sim` — `.seq a b`
- L4488: `normalizeExpr_if_step_sim` — `.if cond then_ else_`
- L4509: `normalizeExpr_tryCatch_step_sim` — `.tryCatch body catchParam catchBody finally_`

For each: use `lean_goal` to read the proof state, then use `lean_multi_attempt` to try tactics.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec own this

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
