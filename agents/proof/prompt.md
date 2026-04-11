# proof — CLOSE HasReturnInHead_step_error_isLit (L14157)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE lemma, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T11:30
- ANF: 33 sorries. CC: 15 (jsspec). Total: 48.
- **HasReturnInHead_step_nonError WRITTEN** (wasmspec, ~600 lines) — depends on step_error_isLit
- **HasReturnInHead_Steps_steppable (L14161) PROVED** — depends on step_error_isLit
- Closing step_error_isLit cascades: -4 to -8 sorries

## ⚠️ DO NOT WORK ON:
- L10429-L10800 (trivialChain — LSP TIMEOUT zone)
- L12969-L14148 (wasmspec-owned HasReturnInHead_step_nonError)
- L15033-L15810 (while/if — BLOCKED)
- L16651-L16672 (tryCatch — BLOCKED)
- L17999, L18010 (noCallFrameReturn/body_sim — BLOCKED)

## P0: HasReturnInHead_step_error_isLit (L14157) — CASCADE BLOCKER

```lean
private theorem HasReturnInHead_step_error_isLit
    {sf sf' : Flat.State} {msg : String}
    (hret : HasReturnInHead sf.expr)
    (hstep : Flat.step? sf = some (.error msg, sf')) :
    ∃ v, sf'.expr = .lit v
```

### KEY INSIGHT: HasReturnInHead has NO tryCatch/while_ constructor

Look at L7239-7273. HasReturnInHead constructors cover: return, seq, let, getProp, setProp, binary, unary, typeof, deleteProp, assign, call, newObj, if_cond, throw, yield, await, getIndex, setIndex, getEnv, makeClosure, makeEnv, objectLit, arrayLit.

**NO tryCatch**, **NO while_**, **NO var**, **NO this**, **NO functionDef**.

This is critical because the ONLY case in Flat.step? where an error step does NOT produce `.lit v` is the tryCatch catch case (Semantics.lean L1109-1111) where the catch handler becomes the new expression. Since HasReturnInHead excludes tryCatch, this case is impossible.

### PROOF STRATEGY

**Approach: Well-founded induction on Flat.Expr.depth** (same as step_nonError at L13623).

For each HasReturnInHead constructor:
1. **Leaf cases** (return_none_direct, return_some_direct): step? directly produces `.lit v`
   - `.return none` → `{ expr := .lit .undefined }` ✓
   - `.return (some v)` where v is value → `{ expr := .lit v }` ✓
   - `.return (some e)` where e not value → steps sub-expr, error propagates with `si.expr`

2. **Compound cases** (seq_left, let_init, assign_val, etc.):
   - `HasReturnInHead_not_value _ h` (L7364) shows sub-expr is NOT a value
   - So `exprValue? sub = none`, step? recurses on sub-expr
   - If sub-step is error: `s'.expr = si.expr`, and by IH `si.expr = .lit v` ✓
   - If sub-step is not error: the outer step is NOT an error (contradiction with `hstep`)

3. **Impossible cases**: tryCatch, while_, var, this, functionDef — HasReturnInHead can't hold

### CONCRETE TACTIC SKETCH

```lean
  cases sf with | mk e env heap trace funcs cs =>
  simp only [Flat.State.expr] at hret
  -- Strong induction on depth
  have hd := Flat.Expr.depth_pos e  -- or use Nat.strongRecOn
  induction e using Flat.Expr.depth.induction with  -- or whatever the WF induction is
  | ... =>
    -- For each HasReturnInHead case, unfold step?
    match hret with
    | .return_none_direct =>
      simp [Flat.step?, Flat.pushTrace, Flat.State.expr] at hstep ⊢
      exact ⟨.undefined, rfl⟩
    | .return_some_direct =>
      simp [Flat.step?] at hstep
      -- case split on exprValue? v
      ...
    | .seq_left h =>
      have hv := HasReturnInHead_not_value _ h
      simp [Flat.step?, hv] at hstep
      -- hstep now says step? {expr := a} produced error
      -- apply IH to sub-expression
      ...
```

### IMPORTANT DETAILS

1. `pushTrace` (Semantics.lean L191) only modifies `trace`, NOT `expr`. So `s'.expr` equals whatever was set in the record update.

2. For compound error propagation, step? does:
   ```
   match step? { s with expr := sub } with
   | some (.error _, si) =>
       some (t, pushTrace { s with expr := si.expr, ... } t)
   ```
   So `sf'.expr = si.expr`. By IH on `si`, `si.expr = .lit v`.

3. The IH needs depth to decrease. For compound constructors like `.seq a b`, `step? {expr:=a}` has `a.depth < (.seq a b).depth`. This matches the pattern in step_nonError.

4. **Try `lean_multi_attempt` first** at L14157:
   ```
   ["cases sf with | mk e env heap trace funcs cs => simp only [Flat.State.expr] at hret; cases hret <;> simp [Flat.step?, Flat.exprValue?, Flat.pushTrace, Flat.State.expr] at hstep ⊢ <;> sorry",
    "cases hret <;> simp_all [Flat.step?, Flat.exprValue?, Flat.pushTrace, Flat.State.expr]"]
   ```

## P1: Complete break/continue non-head cases (L4671, L5809)

After P0, if time permits. These are the 13 non-head constructors in HasBreakInHead_step?_produces_error and HasContinueInHead_step?_produces_error.

## P2: L18229 and L18300

End-of-file sorries. Check context and assess.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasReturnInHead_step_error_isLit" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
