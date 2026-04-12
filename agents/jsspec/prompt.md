# jsspec — CCStateAgree: GLOBAL INVARIANT CHANGE

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T07:30
- CC: **12** real sorries. Total: **42** (ANF 30 + CC 12).
- convertExpr_expr_eq_of_funcs_size infrastructure DONE.
- CCStateAgree analysis complete: global invariant change IS needed.

## YOUR TARGET: 6 CCStateAgree sorries

These are the sorries you can close:
- L7136 (if-true CCStateAgree)
- L7162 (if-false CCStateAgree)
- L10048 (tryCatch CCStateAgree)
- L10051 (tryCatch body-value with finally)
- L10125 (CCStateAgree after conversion)
- L10241 (while_ CCStateAgree)

## THE APPROACH: Weaken CCStateAgree to drop nextId

From your analysis: the ONLY field that causes mismatch is `nextId`. `funcs` and `names` stay deterministic.

**Option C (RECOMMENDED):** Define:
```lean
def CCStateAgreeWeak (st_real st_sim : CCState) : Prop :=
  st_real.funcs = st_sim.funcs ∧ st_real.names = st_sim.names
  -- nextId can differ
```

Then change the suffices block (L6411-6413) to use CCStateAgreeWeak instead of CCStateAgree.

### EXECUTION:
1. `lean_goal` at L7136 to see the EXACT current goal
2. Define CCStateAgreeWeak near CCStateAgree
3. Try replacing CCStateAgree with CCStateAgreeWeak in the suffices for ONE sorry (L7136)
4. If the goal becomes provable, extend to the other 5

### IMPORTANT: Test on ONE sorry FIRST
Don't change the whole invariant globally until you've confirmed ONE case works.
The risk is that weakening the invariant makes OTHER (currently-proved) cases break.

## DO NOT TOUCH:
- L6688, L7993, L8004 (multi-step — architectural, different class)
- L7785 (unclassified)
- L8644 (getIndex — UNPROVABLE)
- L9891 (functionDef — multi-step)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
