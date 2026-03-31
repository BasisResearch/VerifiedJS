# jsspec — Fix CC sorry regression (38 → reduce)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## SITUATION
- **CC: 38 sorries, BUILD PASSES.** Extra sorries added to fix cascading errors. Many fixable.
- **ANF: 58 sorries — FILE LOCKED** (owned by proof, group read-only). DO NOT TOUCH.
- **LowerCorrect: FILE LOCKED.** DO NOT TOUCH.

## YOUR PLAN: Fix CC sorry regressions

### Priority 1: Fix helper theorems (L2059, L2072)
**L2059** (`Flat_step?_call_consoleLog_vals`): `Flat.pushTrace` is private.
- The @[simp] lemma `Flat.step?_pushTrace_expand` should fire automatically
- Try: `unfold Flat.step?; simp [Flat.exprValue?, hvals, Core.consoleLogIdx]`
- The `let msg := match ...` in the conclusion creates a dependent match pattern
- May need to use `show` to specialize the match, or `split` on argVals

**L2072** (`Core_step?_call_consoleLog_general`): `Core.pushTrace` IS public.
- Same dependent match issue
- Try: `unfold Core.step?; simp [Core.exprValue?, hargs, Core.consoleLogIdx]; unfold Core.pushTrace; rfl`

### Priority 2: Restore call non-function case (L4129)
Was previously proven. Needs restoring after hsf_eta parentheses fix:
- `lean_goal` to see current state
- Pattern: hsf_eta sets sf.expr, rw at hstep, Flat_step?_call_nonclosure, Core.step_call_nonfunc_exact
- All 10 refine bullets are standard: hinj, henvCorr, henvwf, hheapvwf, hheapna, noCallFrameReturn, ExprAddrWF, CCState

### Priority 3: Fix setProp/setIndex sorry bullets (L4590-4596, L5084-5092)
Individual proof bullets sorry'd. For each:
1. `lean_goal` at the sorry line
2. `lean_multi_attempt` with: `["exact hheapna'", "simp [sc', hheapna]", "simp [sc', noCallFrameReturn]", "simp [sc', ExprAddrWF, ValueAddrWF]"]`

### Priority 4: Fix tryCatch sorries (L5710-5718)
- L5710: `catchParam ≠ "__call_frame_return__"` — extract from hncfr via noCallFrameReturn tryCatch
- L5711-5712: `noCallFrameReturn body/catchBody` — extract from hncfr

### SKIP (architecturally blocked):
- L1507-1508: forIn/forOf stubs
- L3258: captured var (HeapInj)
- L3586, L3609: CCStateAgree
- L4298: newObj
- L4876: getIndex semantic mismatch
- L5416, L5516: heap allocation
- L5610: functionDef
- L5750: while_ CCState

## WORKFLOW:
1. `grep -n sorry ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
