# proof — Write Flat.Steps_lift + close throw compound cases

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell string)

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (19:05 Mar 30)
- ANF: 18 sorries
  - 7 depth-induction (L3825-3923) — skip for now
  - 2 consolidated context (L4116, L4327) — skip for now
  - 2 throw remaining (L4452, L4455) — **YOUR TARGET**
  - 7 expression-case theorems (L4486-L4625) — NEXT TARGET

## YOUR CRITICAL BLOCKER: Step-lifting through compound contexts

ALL remaining expression-case sorries share the same blocker: when normalizeExpr sees
a compound expression like `.seq a b` or `.let name init body`, it processes the first
sub-expression and wraps the result. The Flat steps for the inner sub-expression need
to be "lifted" through the outer compound context.

### PRIORITY 1: Write a general `Flat.Steps_ctx` lemma

You need a lemma that says: if `Flat.Steps {s | expr := inner} evs {s' | expr := inner'}`
(where inner steps to inner'), then for a compound context C (like `.throw _`, `.seq _ b`,
`.let name _ body`, `.unary op _`), `Flat.Steps {s | expr := C inner} evs {s' | expr := C inner'}`.

**Pattern**: For each context C, you already have `step?_C_ctx` (written in the 13:30 run):
- `step?_throw_ctx`, `step?_seq_ctx`, `step?_let_init_ctx`, etc.

The `Steps_ctx` lemma lifts single-step ctx to multi-step:

```lean
private theorem Flat.Steps_throw_ctx
    (sf : Flat.State) (evs : List Core.TraceEvent) (sf' : Flat.State)
    (hsteps : Flat.Steps { sf with expr := inner } evs { sf' with expr := inner' })
    (hnoerr : ∀ ev ∈ evs, ∀ msg, ev ≠ .error msg) :
    Flat.Steps { sf with expr := .throw inner } evs { sf' with expr := .throw inner' } := by
  induction hsteps with
  | refl _ => exact .refl _
  | tail hstep ih =>
    -- Use step?_throw_ctx for single step, ih for rest
    sorry -- Fill in
```

Write this for `.throw`, `.seq _ b` (left position), `.let name _ body` (init position),
`.unary op _`, `.return (some _)`, `.yield (some _)`, `.await _`.

### PRIORITY 2: Close L4452 (throw compound cases)

Once you have `Steps_throw_ctx`, L4452 becomes:
1. The compound flat_arg (e.g., `.seq a b`) is processed by normalizeExpr
2. normalizeExpr of compound expressions first evaluates sub-expressions via recursive calls
3. Each recursive call produces `Flat.Steps` on the sub-expression
4. `Steps_throw_ctx` lifts these through the `.throw _` wrapper

The key insight: normalizeExpr processes compound expressions by first evaluating them to
a trivial value (using fresh variables). The Flat steps for this evaluation are exactly the
steps that `normalizeExpr_labeled_step_sim` constructs (it already handles compound expressions).
So you can REUSE that infrastructure.

Specifically, for `.throw (.seq a b)`:
- normalizeExpr (.throw (.seq a b)) k = normalizeExpr (.seq a b) (fun t => pure (.throw t))
- normalizeExpr (.seq a b) k' first steps through a, then b, producing trivial t
- Then k' t = pure (.throw t), so result is .throw t
- The Flat steps: step through a, then b (inside .throw context), then throw the result

### PRIORITY 3: Close L4455 (HasThrowInHead non-direct)

HasThrowInHead cases: `.seq (.throw _) b`, `.let name (.throw _) body`, etc.
For these, the throw is in head position of a compound expression:
- Flat.step? on `.seq (.throw (.lit v)) b` = step? on `.throw (.lit v)` via seq_left
- So the throw fires through the compound context

Use the existing `step?_seq_error`, `step?_let_init_error` helpers.

### PRIORITY 4: Close normalizeExpr_return_step_sim (L4486)

Same pattern as throw: `.return (some arg)` evaluates arg then fires return.
The step?_return_some_ctx + Steps lifting handles compound args.
For none case: `.return none` → Flat steps to `.lit .undefined` with error trace.

## DO NOT TOUCH:
- Depth-induction cases (L3825-3923)
- Consolidated context cases (L4116, L4327)
- ClosureConvertCorrect.lean — jsspec and wasmspec own this

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
