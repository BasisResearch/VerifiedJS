# proof — UNCOMMENT AND FIX NoNestedAbrupt_step_preserved (L14468)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- hasAbruptCompletion_step_preserved: **PROVED** (well done!). Termination + all cases work.
- NoNestedAbrupt_step_preserved (L14468): still `sorry`, with commented-out proof L14469-L14986.
- ANF: 39 real sorries. CC: 15. Total: 54.

## P0: UNCOMMENT NoNestedAbrupt_step_preserved (L14468-14986)

The commented proof at L14469-14986 was working before Flat.step? error propagation changes. It needs the same fix pattern you used in hasAbruptCompletion.

**EXACT STEPS:**
1. Delete `sorry -- TODO: fix for error propagation; cases need split at hstep for match t with` at L14468
2. Change `/-obtain` at L14469 to `obtain` (remove the `/-`)
3. Delete the closing `-/` at L14986

This will uncomment the proof. It will have errors because each sub-expression stepping case now has THREE branches instead of TWO:
- **Old**: `split at hstep` → (non-error step, none)
- **New**: `split at hstep` → (error event, non-error step, none)

For each case where `split at hstep` breaks a step?-body result:
- The **error branch** is NEW. In hasAbruptCompletion you handled it with `simp [Flat.pushTrace, hasAbruptCompletion]`. For NoNestedAbrupt, the error branch should be:
  ```lean
  · split at hstep <;> (obtain ⟨_, rfl⟩ := hstep; simp [Flat.pushTrace]; exact .lit)
  ```
  OR simply: the error produces `.lit` (error-as-value), so `NoNestedAbrupt.lit` applies.

**PATTERN from hasAbruptCompletion**: In that proof, each sub-expression case after `split at hstep` has:
```lean
· -- error event
  split at hstep  -- isCallFrame check
  · split at hstep <;> (obtain ⟨_, rfl⟩ := hstep; simp [Flat.pushTrace, ...])
  · ...
· -- non-error step (this is what the old proof had)
  split at hstep <;> { obtain ⟨_, rfl⟩ := hstep; simp [Flat.pushTrace]; ... IH ... }
· exact absurd hstep (by simp)
```

For NoNestedAbrupt, the error branch is SIMPLER: error produces a value (.error msg is stored as .lit), so the result satisfies NoNestedAbrupt.lit.

**ALSO ADD** termination hint after the proof (same as hasAbruptCompletion):
```lean
termination_by Flat.Expr.depth e
decreasing_by all_goals (simp_all [Flat.Expr.depth, Flat.Expr.listDepth, Flat.Expr.propListDepth]; omega)
```

**EXPECTED RESULT**: -1 sorry (L14468 closed). If termination succeeds, L15394/L15465 may cascade.

## P1: AFTER P0 — CHECK L15394 AND L15465

These sorries may depend on NoNestedAbrupt_step_preserved. Run `lean_goal` at those lines. If they become provable after P0, close them.

## SKIP: labeled_branch (blocked), CC (jsspec), while/tryCatch, if_branch, anfConvert_step_star

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — NoNestedAbrupt L14468" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
