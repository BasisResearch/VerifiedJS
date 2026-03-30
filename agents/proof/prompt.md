# proof — Close ANF expression-case sorries (throw first)

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell string)

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (17:05 Mar 30)
- ANF: 17 sorries, 3 groups:
  - 7 depth-induction (L3825-3923) — skip for now
  - 2 consolidated context (L4116, L4327) — skip for now
  - 8 expression-case: **YOUR TARGET**
    - L4368: normalizeExpr_throw_step_sim (PRIORITY 1)
    - L4399: normalizeExpr_return_step_sim
    - L4423: normalizeExpr_await_step_sim
    - L4454: normalizeExpr_yield_step_sim
    - L4475: normalizeExpr_let_step_sim
    - L4496: normalizeExpr_seq_step_sim
    - L4517: normalizeExpr_if_step_sim
    - L4538: normalizeExpr_tryCatch_step_sim

## PRIORITY 1: Write `hasThrowInHead_flat_error_steps` + close throw case (L4368)

### Step 1: Write the helper (insert BEFORE L4340, after HasThrowInHead_not_value)

The throw case needs a multi-step helper like `hasBreakInHead_flat_error_steps`. Unlike break (1 step), throw evaluates its argument first, then emits the error. Structure:

```lean
/-- If HasThrowInHead e, then Flat steps evaluate to either:
    - error msg (if throw arg evaluates to value v, msg = valueToString v), or
    - error msg (if throw arg sub-step errors) -/
private theorem hasThrowInHead_step?_error_aux
    (d : Nat) (e : Flat.Expr) (hd : e.depth ≤ d)
    (h : HasThrowInHead e)
    (sf : Flat.State) (hsf : sf.expr = e) :
    -- At minimum: one step exists (not stuck), and it's either:
    -- (a) an error event (throw arg is value → immediate), or
    -- (b) a sub-stepping event (throw arg not value → arg steps)
    ∃ s' ev, Flat.step? sf = some (ev, s') := by
  induction d generalizing e sf with
  | zero => cases h <;> simp [Flat.Expr.depth] at hd
  | succ d ih =>
    cases h with
    | throw_direct =>
      -- sf.expr = .throw arg
      -- Flat.step? on .throw: either exprValue? arg = some v → error, or step arg
      cases sf with | mk expr env heap trace funcs cs =>
      simp only [Flat.State.expr] at hsf; subst hsf
      simp only [Flat.step?]
      -- case split on exprValue? arg
      sorry  -- FILL IN: cases on exprValue? arg, then cases on step?
    | seq_left hsub =>
      cases sf with | mk _ env heap trace funcs cs =>
      simp only [Flat.State.expr] at hsf; subst hsf
      have hnotval := HasThrowInHead_not_value _ hsub
      -- ... same pattern as hasBreakInHead_step?_error_aux
      sorry
    -- ... repeat for each HasThrowInHead constructor
    | _ => sorry
```

**BUT ACTUALLY**: The throw case is simpler than you think. Look at the existing `normalizeExpr_throw_step_sim` signature (L4340-4368). It takes `HasThrowInHead` as given (via `normalizeExpr_throw_implies_hasThrowInHead`). The proof needs to:

1. Use `ANF.normalizeExpr_throw_implies_hasThrowInHead` to get `HasThrowInHead sf.expr`
2. Induct on the HasThrowInHead proof (same as break/continue pattern)
3. For `throw_direct`: `sf.expr = .throw arg`.
   - `exprValue? arg = some v` → one Flat step produces `.error (valueToString v)`. The ANF side has `evalTrivial sf.env arg = .ok v` (from hnorm inversion). Match traces.
   - `exprValue? arg = none` → arg is not a value, but normalizeExpr produced `.throw arg` with arg being a trivial. Trivials ARE values in Flat. So `exprValue? arg = some v` always. This case may be vacuous.
4. For compound cases (seq_left, let_init, etc.): step through the outer expression context, then recurse.

### Key insight: trivial args are always Flat values
In `normalizeExpr_throw_step_sim`, `arg : ANF.Trivial`. After ANF conversion, the throw argument is already a trivial (variable or literal). When we map back to Flat, the corresponding Flat sub-expression is a value (literal or var lookup). So `exprValue?` on the Flat throw arg should always succeed → the throw is a single Flat step.

### Step 2: Use it to prove L4368

```lean
-- At L4368, replace sorry with:
  have hthrow := ANF.normalizeExpr_throw_implies_hasThrowInHead sf.expr k hk arg n m hnorm
  -- Now induct on hthrow to construct Flat.Steps
  -- For throw_direct: sf.expr = .throw farg for some farg
  --   normalizeExpr (.throw farg) k produces .throw (trivialOfFlat farg)
  --   So farg maps to arg under the trivial conversion
  --   Flat.step? evaluates .throw farg:
  --     exprValue? farg = some v → .error (valueToString v) in one step
  --     Then match with evalTrivial sf.env arg = .ok v
  sorry -- fill in the actual tactic proof
```

Use `lean_goal` at L4368 to see the exact proof state. Then try `lean_multi_attempt` with various approaches. The `throw_direct` case is the base; compound cases follow the break pattern.

## PRIORITY 2: Close return case (L4399) — same pattern as throw

`normalizeExpr_return_step_sim` is analogous. Return with `some arg` evaluates arg (trivial → value → one step). Return with `none` is immediate.

## PRIORITY 3: Close await (L4423) and yield (L4454) — similar

## LOWER PRIORITY: let/seq/if/tryCatch (L4475-4538) — harder, need CPS context inversion

## DO NOT TOUCH:
- Depth-induction cases (L3825-3923)
- Consolidated context cases (L4116, L4327)
- ClosureConvertCorrect.lean — jsspec and wasmspec own this

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
