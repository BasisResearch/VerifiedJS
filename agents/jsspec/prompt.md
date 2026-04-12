# jsspec — CCStateAgree: CLOSE THE 6 SORRIES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T08:05
- CC: **12** real sorries. Total: **42** (ANF 30 + CC 12).
- You removed hid requirement from convertExpr_CCExprEquiv_shifted. Good.
- convertExpr_expr_eq_of_funcs_size infrastructure DONE.
- You keep crashing. STOP CRASHING. Keep tasks SMALL.

## YOUR TARGET: 6 CCStateAgree sorries

- L7136 (if-true CCStateAgree)
- L7162 (if-false CCStateAgree)
- L10048 (tryCatch CCStateAgree)
- L10051 (tryCatch body-value with finally)
- L10125 (CCStateAgree after conversion)
- L10241 (while_ CCStateAgree)

## THE ROOT CAUSE (from your own analysis)

After branching (if/while/tryCatch), the taken branch state diverges from the simulation state
by `exprFuncCount(skipped_branch)` in both `nextId` and `funcs.size`.

CCStateAgree requires EXACT equality of all fields. This fails for nextId and funcs.

## APPROACH: CCStateAgreeWeak

**Option 1 — Weaken globally (risky but complete):**
```lean
def CCStateAgreeWeak (st_real st_sim : CCState) : Prop :=
  st_real.funcs = st_sim.funcs ∧ st_real.names = st_sim.names
```
Replace CCStateAgree with CCStateAgreeWeak in the suffices block (L6411-6413).
Risk: may break currently-proved cases that rely on full state equality.

**Option 2 — Local fix with convertExpr_expr_eq_of_funcs_size (safer):**
At each sorry site, the goal is `CCStateAgree st' st_a'` where st_a' skips a branch.
Instead of proving full CCStateAgree, prove:
- `st'.funcs = st_a'.funcs` (follows from convertExpr_state_determined + both branches add same funcs)
- `st'.names = st_a'.names` (names don't change in convertExpr)
- Accept that nextId differs

For Option 2, you need to change the suffices invariant to NOT require CCStateAgree but instead
require only funcs/names agreement. This is essentially Option 1 under a different name.

**Option 3 — Prove funcs equality despite state gap:**
Key insight from convertExpr_state_delta: `convertExpr e ... st` adds exactly `exprFuncCount e` to
both nextId and funcs.size. So `st_taken.funcs.size = st_orig.funcs.size + exprFuncCount(taken_branch)`.
If the simulation state `st_a` starts with the SAME funcs array (not just size), then after conversion:
`st_a'.funcs = st'.funcs` because both add the same function definitions (by convertExpr_state_determined).
The ONLY difference is nextId. So funcs/names equality IS preserved through branching.

### EXECUTION (START WITH ONE SORRY):
1. `lean_goal` at L7136 to see the exact goal shape
2. Try `exact ⟨rfl, rfl⟩` or `constructor <;> rfl` — maybe funcs/names are definitionally equal?
3. If not, check what the actual goal is after `sorry` at L7136
4. If CCStateAgree is `st.funcs = st_a.funcs ∧ st.names = st_a.names ∧ st.nextId = st_a.nextId`,
   the first two conjuncts may be provable and only nextId fails
5. If so: define CCStateAgreeWeak, change suffices, test on L7136

**DO NOT** attempt global changes until ONE sorry is confirmed solvable.

## DO NOT TOUCH:
- L6688, L7993, L8004 (multi-step — architectural)
- L7785 (unclassified)
- L8644 (AXIOM — unprovable)
- L9891 (functionDef — multi-step)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
