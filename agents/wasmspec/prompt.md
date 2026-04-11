# wasmspec — CLOSE HasReturnInHead_step_nonError (L13260) + error_isLit (L13268)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T10:00
- Total: 47 sorries (ANF 32, CC 15). UP by 1 from 46 due to your decomposition (1 sorry → 2).
- The sorry at old L13264 was decomposed into L13260 (HasReturnInHead_step_nonError) + L13268 (HasReturnInHead_step_error_isLit).
- HasReturnInHead_Steps_steppable (L13272) already has its proof structure (induction with refl/tail cases). It just needs the two sub-lemmas.
- Remaining wasmspec-owned: L12969, L13260, L13268, L13464, L13820, L13993, L14049, L14053, L14054 = 9 sorries

## P0: HasReturnInHead_step_nonError (L13260) — HIGHEST PRIORITY (-1 sorry)

```lean
private theorem HasReturnInHead_step_nonError
    {sf sf' : Flat.State} {t : Core.TraceEvent}
    (hret : HasReturnInHead sf.expr)
    (hstep : Flat.step? sf = some (t, sf'))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    HasReturnInHead sf'.expr
```

### PROOF APPROACH: Induction on `hret`

**Key insight**: HasReturnInHead e implies e is NOT a flat value (no constructor for .lit). So compound expressions always delegate step to the head sub-expression.

**Base cases** — produce ERROR events → contradiction with hnoerr:
1. `return_none_direct`: sf.expr = .return none. step? produces (.error "return:undefined", ...). Contradiction with hnoerr. Use `exfalso`.
2. `return_some_direct`: sf.expr = .return (some v).
   - If v is a value (.lit): step? produces (.error "return:v_str", ...). Contradiction.
   - If v is NOT a value: step? delegates to step v. Result = .return (some v'). HasReturnInHead (.return (some v')) by return_some_direct. **Done without IH**.

**Compound cases** — step delegates, IH applies:
3. `seq_left h`: sf.expr = .seq a b, HasReturnInHead a. a is not a value (HasReturnInHead → not lit). step? delegates to step a. sf'.expr = .seq a' b. Event = event from stepping a (still non-error by hnoerr). By IH: HasReturnInHead a'. Then `seq_left` gives HasReturnInHead (.seq a' b).

4. `seq_right h`: sf.expr = .seq a b, HasReturnInHead b.
   - If a not value: step? delegates to a. sf'.expr = .seq a' b. b unchanged → `seq_right h`.
   - If a is value (.lit v): step? (.seq (.lit v) b) = (.silent, ⟨b, ...⟩). sf'.expr = b. HasReturnInHead b = h. Done.

5. Same pattern for: let_init, binary_lhs, binary_rhs, unary_arg, typeof_arg, assign_val, deleteProp_obj, getProp_obj, setProp_obj, setProp_val, if_cond, call_func, call_env, call_args, newObj_*, getIndex_*, setIndex_*, getEnv_env, makeClosure_env, makeEnv_values, objectLit_props, arrayLit_elems.

6. **throw_arg h**: sf.expr = .throw arg, HasReturnInHead arg.
   - If arg is value: step? produces (.error "Uncaught:...", ...). Contradiction with hnoerr.
   - If arg not value: step? delegates. sf'.expr = .throw arg'. By IH HasReturnInHead arg'. Then throw_arg gives result.

7. **yield_some_arg h, await_arg h**: Same pattern as throw_arg.

### STEP-BY-STEP
1. `lean_goal` at L13260
2. Start: `induction hret with` (or `cases hret` + recursive calls)
3. Base cases: unfold step?, show contradiction with hnoerr
4. Compound cases: unfold step?, show delegation, apply IH
5. Use `lean_multi_attempt` on individual cases if stuck

### IMPORTANT: Lean 4 mutual induction
If HasReturnInHead is in a `mutual` block with HasReturnInHeadList/HasReturnInHeadProps, you may need `mutual` recursion. Check with lean_hover_info on HasReturnInHead to see if it's mutual.

## P1: HasReturnInHead_step_error_isLit (L13268) — (-1 sorry)

```lean
private theorem HasReturnInHead_step_error_isLit
    {sf sf' : Flat.State} {msg : String}
    (hret : HasReturnInHead sf.expr)
    (hstep : Flat.step? sf = some (.error msg, sf')) :
    ∃ v, sf'.expr = .lit v
```

**Approach**: Similar induction on `hret`.
- Base: return_none → sf'.expr = .lit .undefined. return_some with value arg → sf'.expr = .lit v.
- Compound: step delegates. The error event comes from the sub-step. By IH on sub, sf_sub'.expr = .lit v. But the compound WRAPS the result: sf'.expr = .compound_constructor (.lit v) rest.

**WAIT**: This means sf'.expr = .lit v is FALSE for compound cases! If sf.expr = .seq a b and step delegates to step a producing (.error msg, ⟨.lit v, ...⟩), then sf'.expr = .seq (.lit v) b, NOT .lit v.

**CHECK**: Does the actual Flat.step? for .seq propagate errors differently? Some semantics have error propagation where the entire compound becomes the error result. Use `lean_hover_info` or `lean_goal` to check what step? (.seq a b) produces when step? a produces an error.

**If theorem is FALSE**: The theorem needs modification. Options:
- Change to `∃ v, Flat.exprValue? sf'.expr = some v` (whole expression is a value)
- Change to weaker: the error event still implies callStack safety
- Or: prove the callStack conditions directly instead of going through HasReturnInHead

## P2: After P0+P1, L13464 compound HasReturnInHead (-1)
## P3: L13820 HasAwaitInHead, L13993 HasYieldInHead (-2)
## P4: L14049, L14053, L14054 return/yield .let (-3)

## SKIP (BLOCKED or proof-owned):
- L10183-L10554 (trivialChain — proof agent)
- L14144-14921 (while/if — BLOCKED)
- L15762-15783 (tryCatch — BLOCKED)
- L17110-17411 (BLOCKED)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasReturnInHead_step_nonError L13260" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
