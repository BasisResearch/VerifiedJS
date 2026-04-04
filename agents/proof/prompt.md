# proof — Close L7791 (EndToEnd param) + hasAbruptCompletion_step_preserved

## RULES
- Edit: ANFConvertCorrect.lean AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build EndToEnd: `lake build VerifiedJS.Proofs.EndToEnd`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## MAJOR PROGRESS — NoNestedAbrupt 15/22 cases DONE

You have already closed 15 NoNestedAbrupt cases (seq, let, assign, if, throw, return, await, yield, getProp, deleteProp, typeof). Supervisor closed 8 more (unary, binary, while_, labeled, setProp, getIndex, getEnv, makeClosure). Only 7 sorry remain: setIndex, call, newObj, makeEnv, objectLit, arrayLit, tryCatch. These are list/complex cases — PARK THEM for now.

## TASK 1 (PRIORITY): Close L7791 in ClosureConvertCorrect.lean via EndToEnd.lean

L7791 in ClosureConvertCorrect.lean is:
```lean
  have h_supp : s.body.supported = true := sorry
```
inside `closureConvert_correct`. The fix requires TWO coordinated edits:

### Step A: Add param to closureConvert_correct (ClosureConvertCorrect.lean)

Change the theorem signature from:
```lean
theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (hnofor : ...) :
```
to:
```lean
theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (h_supp : s.body.supported = true)
    (hnofor : ...) :
```
And DELETE the sorry line `have h_supp : s.body.supported = true := sorry`.

### Step B: Update EndToEnd.lean callsite

In `flat_to_wasm_correct`, add `(h_supp_core : core.body.supported = true)` after `h_addr_wf`, and pass it at the callsite on L70:
```lean
    obtain ⟨coreTrace, hcoreb, heq⟩ := closureConvert_correct core flat hcc h_wf h_addr_wf h_supp_core hnofor flatTrace hflatb
```

Build BOTH files after.

## TASK 2: Close hasAbruptCompletion_step_preserved (L9209)

L9209: `sorry -- SEPARATE THEOREM: prove later by same induction pattern`

This theorem says: if `hasAbruptCompletion expr = false` and `Flat.step?` succeeds, then the result also has `hasAbruptCompletion = false`. It follows the EXACT same induction-on-depth structure as `NoNestedAbrupt_step_preserved`. Each case: unfold step?, split on exprValue?, value case → .lit (hasAbruptCompletion false by def), sub-step case → recursive call.

The `hasAbruptCompletion` function returns true only for break/continue/return/throw/yield/await with nested abrupt. For all other constructors, it recurses on sub-expressions. Use the same `ih` pattern.

## TASK 3 (IF TIME): Close remaining NoNestedAbrupt list cases

The 7 remaining cases (setIndex, call, newObj, makeEnv, objectLit, arrayLit, tryCatch) need `firstNonValueExpr`/`firstNonValueProp` induction. These are optional — focus on Tasks 1-2 first.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
