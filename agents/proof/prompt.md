# proof — Close the 14 remaining NoNestedAbrupt sorry cases

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

## STATE: NoNestedAbrupt_step_preserved has skeleton filled for simple/medium cases. 14 sorry cases remain at L9286-9334.

## TASK: Close all 14 sorry cases by copying the getProp pattern

### TEMPLATE — getProp (already proved at L9268-9282):
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

### GROUP 1: Single-sub-expression (same as getProp exactly)
- `deleteProp obj prop` — same as getProp. Replace L9298 sorry.
- `typeof arg` — same as getProp but with `typeof`/`harg`. Replace L9302 sorry.

### GROUP 2: Two-sub-expression (obj + val/idx)
- `setProp obj prop val` (L9286) — step? checks obj first, then val. Pattern:
```lean
    | setProp obj prop val =>
      cases hna with | setProp hobj hval =>
      simp [Flat.step?] at hstep
      split at hstep
      case h_1 vo hvo =>
        -- obj is value
        split at hstep
        case h_1 vv hvv =>
          -- val is value
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]; exact NoNestedAbrupt.lit
        case h_2 hvv =>
          split at hstep
          case h_1 ev' sv hsv =>
            simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
            simp [Flat.State.expr]
            exact NoNestedAbrupt.setProp (by simp [Flat.Expr.isValue] at hvo; exact noNestedAbrupt_of_isValue hvo)
              (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hval hsv)
          case h_2 => simp at hstep
      case h_2 hvo =>
        split at hstep
        case h_1 ev' so hso =>
          simp [Flat.pushTrace] at hstep; obtain ⟨_, rfl⟩ := hstep
          simp [Flat.State.expr]
          exact NoNestedAbrupt.setProp
            (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hobj hso)
            hval
        case h_2 => simp at hstep
```

**IMPORTANT**: The exact step? structure depends on how Flat.step? handles each constructor. Use `lean_hover_info` or `lean_goal` after `simp [Flat.step?]` to see the actual splits. The template above is approximate — adjust the split/case structure to match what Lean expects.

- `getIndex obj idx` (L9290) — same two-sub-expression pattern as setProp
- `setIndex obj idx val` (L9294) — three sub-expressions: obj, idx, val

### GROUP 3: Multi-arg (function calls)
- `call f fenv args` (L9306) — most complex. step? checks f, then fenv, then args list. Use split chains.
- `newObj f fenv args` (L9310) — same as call

### GROUP 4: List-based
- `getEnv envExpr idx` (L9314) — two sub-expressions
- `makeEnv vals` (L9318) — list of values
- `makeClosure funcIdx envExpr` (L9322) — two sub-expressions
- `objectLit props` (L9326) — list of (name, expr) pairs
- `arrayLit elems` (L9330) — list of exprs

For list-based: you may need a helper that says "if step? steps one element in a list, NoNestedAbrupt is preserved for the whole list". If this is too complex, leave the sorry but add a comment explaining what's needed.

### GROUP 5: tryCatch
- `tryCatch_some` (L9333) — tryCatch with finally
- `tryCatch_none` (L9334) — tryCatch without finally

For tryCatch: step? on tryCatch evaluates the body. If body is value, catches/finally execute. Use the same IH pattern on the body.

### STRATEGY
1. Do Group 1 first (deleteProp, typeof) — trivial copies of getProp
2. Then Group 2 (setProp, getIndex, setIndex) — slight variation
3. Then Group 4 and 5 as time permits
4. Group 3 last (most complex)

Each closed sorry is progress. Even closing 4 of 14 is good. DO NOT try to close all 14 if memory is tight — close what you can.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
