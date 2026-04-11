# wasmspec — CLOSE HasReturnInHead_step_nonError (L13260) — 30-CASE MUTUAL INDUCTION

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL. Do 5 cases at a time, verify, continue.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T10:30
- Total: 47 sorries (ANF 32, CC 15).
- You started HasReturnInHead_step_nonError at 10:15. CONTINUE.
- Once L13260 is closed → -1. Then L13268 → -1. Then HasReturnInHead_Steps_steppable auto-closes → potential cascade -4 more.
- **This is the highest-value target in the entire project right now.**

## P0: HasReturnInHead_step_nonError (L13260) — DETAILED CASE GUIDE

### Structure: mutual recursion
HasReturnInHead, HasReturnInHeadList, HasReturnInHeadProps are `mutual`. You need MUTUAL well-founded recursion or separate theorems for each.

Write THREE mutually-proved theorems:
```lean
private theorem HasReturnInHead_step_nonError ...
private theorem HasReturnInHeadList_step_nonError ...  -- for call_args, newObj_args, etc.
private theorem HasReturnInHeadProps_step_nonError ... -- for objectLit_props
```

Or use `match` on the HasReturnInHead constructor directly if Lean allows it without mutual.

### Case-by-case guide (30 constructors of HasReturnInHead)

**Pattern A — "Left" compound (head position steps):**
Constructors: seq_left, let_init, getProp_obj, setProp_obj, binary_lhs, unary_arg, typeof_arg, deleteProp_obj, assign_val, call_func, call_env, newObj_func, newObj_env, if_cond, throw_arg, yield_some_arg, await_arg, getIndex_obj, setIndex_obj, getEnv_env, makeClosure_env

For each: the sub-expression `a` has HasReturnInHead. `a` is not a value (HasReturnInHead_not_value). So `Flat.step?` delegates to stepping `a`. After stepping, `a' = sf'.sub_expr`. By IH, `HasReturnInHead a'`. Apply the same constructor to get `HasReturnInHead sf'.expr`.

```lean
| .seq_left h_a =>
  -- sf.expr = .seq a b, HasReturnInHead a
  -- a is not a value, so step? delegates to stepping a
  simp [Flat.step?, HasReturnInHead_not_value _ h_a] at hstep
  -- hstep gives us that step? on a produced (t, ⟨a', ...⟩)
  -- sf'.expr = .seq a' b
  -- By IH: HasReturnInHead a'
  -- Therefore: HasReturnInHead (.seq a' b) by seq_left
  sorry
```

**Pattern B — "Right" compound (non-head position, head is value):**
Constructors: seq_right, binary_rhs, setProp_val, getIndex_idx, setIndex_idx, setIndex_val

For each: the sub-expression with HasReturnInHead is NOT in head position. The head is either a value (step reduces it) or not. Two sub-cases:
- Head not value: step? delegates to head. Sub-expression UNCHANGED. Same constructor applies.
- Head is value: step? evaluates the compound (e.g., .seq (.lit v) b → b). The stepped expression is `b` or the "right" part which has HasReturnInHead.

```lean
| .seq_right h_b =>
  -- sf.expr = .seq a b
  simp [Flat.step?] at hstep
  split at hstep  -- on whether a is a value
  · -- a is value: step gives b directly. HasReturnInHead b = h_b
    sorry
  · -- a is not value: step delegates to a. b unchanged. seq_right h_b.
    sorry
```

**Pattern C — Base cases (return/throw/yield/await):**
- return_none_direct: sf.expr = .return none. step? produces (.error "return:undefined", ...). This is an error → contradiction with hnoerr.
- return_some_direct: sf.expr = .return (some v). If v is value → error → contradiction. If not → step delegates to v → HasReturnInHead v is FALSE (return_some_direct says HasReturnInHead (.return (some v)), not HasReturnInHead v). So sf'.expr = .return (some v') and return_some_direct applies.

**Pattern D — List/Props (mutual):**
- call_args, newObj_args: HasReturnInHeadList args. First non-value arg gets stepped. Need HasReturnInHeadList_step_nonError.
- objectLit_props: HasReturnInHeadProps props. Same pattern.
- makeEnv_values, arrayLit_elems: HasReturnInHeadList values/elems. Same.

### EXECUTION PLAN
1. First batch: base cases (return_none_direct, return_some_direct) — verify with diagnostics
2. Second batch: 5 "left" compound cases (seq_left, let_init, getProp_obj, binary_lhs, unary_arg)
3. Third batch: remaining "left" compounds
4. Fourth batch: "right" compounds (seq_right, binary_rhs, etc.)
5. Fifth batch: list/props mutual cases

**After EACH batch**: `lean_diagnostic_messages` on the theorem. Fix errors before continuing.

### IMPORTANT: Flat.step? definition
Use `lean_hover_info` on `Flat.step?` at L13257 to understand how it handles each expression type. The step function likely pattern-matches on the expression and checks `exprValue?` on sub-expressions.

## P1: HasReturnInHead_step_error_isLit (L13268)
After P0 is done. May need reformulation per wasmspec prompt analysis (compound cases produce .seq (.lit v) b, not .lit v).

## P2-P4: L13464, L13820, L13993, L14049-L14054
After P0+P1 cascade through HasReturnInHead_Steps_steppable.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasReturnInHead_step_nonError continued" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
