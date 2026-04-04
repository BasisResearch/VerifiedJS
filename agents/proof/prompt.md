# proof — Close NoNestedAbrupt sorry cases (L9147-9168)

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## STATE

NoNestedAbrupt_step_preserved at L9107-9168 has a skeleton with 22 sorry cases at L9147-9168. The `zero` base cases and impossible cases (unary, binary, while_, labeled) are done. ALL 22 constructor cases in the `succ` branch are still sorry.

The key context variables available in each case are:
- `n : Nat`, `ih` (induction hypothesis for depth ≤ n)
- `env, heap, trace, funcs, cs` (state components)
- `hd : (expr).depth ≤ n + 1` (depth bound)
- `hna : NoNestedAbrupt expr` (the inductive hypothesis)
- `hstep : Flat.step? {expr, env, heap, trace, funcs, callStack := cs} = some (ev, sf')` (the step)

## TASK: Close sorry cases using these EXACT patterns

### Understanding Flat.step?

`Flat.step?` for most constructors follows: check `exprValue?` on sub-expressions. If value → compute result (`.lit ...`). If not value → recursively step the sub-expression, wrap result in same constructor.

`exprValue?` returns `some v` only for `.lit v`, `none` for everything else.

`pushTrace s t = {s with trace := s.trace ++ [t]}` — just appends to trace.

### PATTERN A: Single sub-expression (assign, getProp, deleteProp, typeof, throw, getEnv, makeClosure)

All follow the same structure. Here is `assign` (L9149):

```lean
    | assign name rhs =>
      cases hna with | assign hval =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        -- exprValue? rhs = some v → result is .lit v
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_2 hv =>
        -- exprValue? rhs = none → sub-step rhs
        split at hstep
        case h_1 ev' sr hsr =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.assign
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hval hsr)
        case h_2 => simp at hstep
```

**getProp** (L9155) — SAME pattern, replace `assign`→`getProp`, `hval`→`hobj`, `name rhs`→`obj prop`:
```lean
    | getProp obj prop =>
      cases hna with | getProp hobj =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_2 hv =>
        split at hstep
        case h_1 ev' so hso =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.getProp
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hobj hso)
        case h_2 => simp at hstep
```

NOTE: getProp has EXTRA splits because `exprValue? obj` branches on `.object addr`, `.string str`, `_`, `none`. The `some _` cases all produce `.lit ...` → `NoNestedAbrupt.lit`. The `none` case does the sub-step. Adjust the split structure to match. You may need:
```lean
      split at hstep  -- exprValue? obj
      case h_1 addr hobj_val =>  -- .object
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_2 str hobj_val =>  -- .string
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_3 hobj_val =>  -- other value
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      case h_4 =>  -- none (sub-step)
        split at hstep
        ...
```

Use `lean_goal` after `simp [Flat.step?] at hstep; split at hstep` to see the actual cases Lean generates.

**deleteProp** (L9159) — same as getProp (splits on exprValue? obj: .object, _, none)
**typeof** (L9160) — same as assign (splits on exprValue? arg: some, none)
**throw** (L9151) — same as assign but `hna` gives `harg : hasAbruptCompletion arg = false`, not `NoNestedAbrupt arg`. You'll need: `cases hna with | throw harg =>`. The sub-step case needs `hasAbruptCompletion_step_preserved` (at L9097, currently sorry). Use `sorry` for the sub-step and add a comment.
**getEnv** (L9163) — splits on exprValue? envExpr: .object, _, none. Value cases → .lit. Sub-step → `NoNestedAbrupt.getEnv (ih ...)`
**makeClosure** (L9165) — splits on exprValue? envExpr: .object, _, none. Value cases → .lit. Sub-step → `NoNestedAbrupt.makeClosure (ih ...)`

### PATTERN B: Two sub-expressions (setProp, getIndex, setIndex)

**setProp** (L9156): step? checks obj first, then val.
```lean
    | setProp obj prop val =>
      cases hna with | setProp hobj hval =>
      simp [Flat.step?] at hstep
      split at hstep  -- exprValue? obj
      case h_1 =>  -- obj not value → step obj
        split at hstep
        case h_1 ev' so hso =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
          exact NoNestedAbrupt.setProp (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hobj hso) hval
        case h_2 => simp at hstep
      case h_2 addr hobjval =>  -- obj = .object addr
        split at hstep  -- exprValue? val
        case h_1 vv hvv =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]; exact NoNestedAbrupt.lit
        case h_2 =>
          split at hstep
          case h_1 ev' sv hsv =>
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
            exact NoNestedAbrupt.setProp (by sorry /- obj is value, use NoNestedAbrupt.lit or similar -/) (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hval hsv)
          case h_2 => simp at hstep
      case h_3 hobjval =>  -- obj = some other value
        -- similar to .object case
        sorry
```

NOTE: The exact split structure for setProp is complex (obj: none→step, .object→(val: some→lit, none→step), other→(val: some→lit, none→step)). Use `lean_goal` to guide you. Even partial progress (proving some sub-cases and sorry-ing others) is valuable.

### PATTERN C: Seq, Let, If

**seq** (L9147):
```lean
    | seq a b =>
      cases hna with | seq ha hb =>
      simp [Flat.step?] at hstep
      split at hstep  -- exprValue? a
      case h_1 v hv =>  -- a is value → result is b
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact hb
      case h_2 hv =>  -- a not value → step a
        split at hstep
        case h_1 ev' sa hsa =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
          exact NoNestedAbrupt.seq (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ ha hsa) hb
        case h_2 => simp at hstep
```

**let** (L9148):
```lean
    | «let» name init body =>
      cases hna with | «let» hinit hbody =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>  -- init is value → substitute
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact hbody
      case h_2 hv =>
        split at hstep
        case h_1 ev' si hsi =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
          exact NoNestedAbrupt.let (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hinit hsi) hbody
        case h_2 => simp at hstep
```

**if** (L9150):
```lean
    | «if» cond then_ else_ =>
      cases hna with | «if» hc hthen helse =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 v hv =>  -- cond is value → branch
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; split <;> assumption  -- if true → hthen, if false → helse
      case h_2 hv =>
        split at hstep
        case h_1 ev' sc hsc =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
          exact NoNestedAbrupt.if (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hc hsc) hthen helse
        case h_2 => simp at hstep
```

### PATTERN D: return, await, yield

**return** (L9152): cases on arg (none/some).
```lean
    | «return» arg =>
      cases arg with
      | none =>
        simp [Flat.step?] at hstep
        simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
        simp [Flat.State.expr]; exact NoNestedAbrupt.lit
      | some a =>
        cases hna with | return_some harg =>
        simp [Flat.step?] at hstep
        split at hstep
        case h_1 v hv =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]; exact NoNestedAbrupt.lit
        case h_2 hv =>
          split at hstep
          case h_1 ev' sa hsa =>
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
            -- Need: hasAbruptCompletion sa.expr = false
            -- This requires hasAbruptCompletion_step_preserved (L9105, currently sorry)
            sorry
          case h_2 => simp at hstep
```

**await** (L9153) and **yield** (L9154) — same pattern as return/some.

### PATTERN E: Lists (makeEnv, objectLit, arrayLit, call, newObj)

These are complex due to `firstNonValueExpr`/`firstNonValueProp`. For now, use sorry with a clear comment:
```lean
    | makeEnv vals =>
      sorry -- needs firstNonValueExpr induction + list membership preservation
    | objectLit props =>
      sorry -- needs firstNonValueProp induction + list membership preservation
    | arrayLit elems =>
      sorry -- needs firstNonValueExpr induction + list membership preservation
    | call f fenv args =>
      sorry -- most complex: 3 sub-expressions + list args
    | newObj f fenv args =>
      sorry -- same as call
```

### PATTERN F: tryCatch (L9168)
```lean
    | tryCatch body param catchBody fin =>
      cases hna with
      | tryCatch_some hbody hcatch hfin => sorry -- body value/step + catch/finally
      | tryCatch_none hbody hcatch => sorry -- body value/step + catch only
```

## STRATEGY — DO THIS IN ORDER
1. **seq** (L9147) — copy exact code above
2. **let** (L9148) — copy exact code above
3. **assign** (L9149) — copy exact code above
4. **if** (L9150) — copy exact code above
5. **getProp** (L9155) — adapt pattern A for multiple value cases
6. **deleteProp** (L9159) — same as getProp
7. **typeof** (L9160) — same as assign
8. Build after every 2-3 cases. Fix errors before continuing.
9. Then do remaining single-sub cases if time permits.
10. Leave list/call/tryCatch cases as sorry with comments.

Even closing 7 of 22 is major progress. DO NOT try to close all 22. Close what you can and move on.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
