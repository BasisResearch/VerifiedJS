# jsspec — CLOSE CCStateAgreeWeak SORRIES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T11:05
- CC file has been RESTRUCTURED. Old CCStateAgree sorries replaced with CCStateAgreeWeak inline pattern.
- The dominant pattern is now: `convertExpr_state_determined ... st_a' sorry /- hAgreeOut.1 -/ sorry /- hAgreeOut.2 -/`
- These provide equality witnesses (`nextId` and `funcs.size`) where only weak inequality (≤) is available.
- **5 old sorries were closed** (CC down from 16 to 11 raw lines, but inline pairs mean more instances).

## THE CORE PROBLEM
`convertExpr_state_determined` requires `st_a'.nextId = st'.nextId` and `st_a'.funcs.size = st'.funcs.size` (equality).
But the IH only gives `CCStateAgreeWeak` which provides ≤.

**The sorries are all of the form**: provide equality proofs for `convertExpr_state_determined` calls.

## SORRY LOCATIONS (grouped by pattern):

**A. `state_determined ... sorry /- hAgreeOut.1 -/ sorry /- hAgreeOut.2 -/` (pairs, ~20 instances):**
- L7141-7146 (let body), L7421 (if cond), L7570 (assign), L7828 (binary lhs)
- L7904 (call f), L8704 (getProp obj), L8998 (setProp obj), L9310 (setIndex)
- L9386 (deleteProp obj)

**B. List/PropList `state_determined` pairs:**
- L8105 (exprList done), L9821 (propList done), L10037 (arrayLit list done)

**C. `hAgreeOut.symm` sorries:**
- L8119-8120, L9836, L10052, L10429

**D. Multi-step gap (3, DO NOT TOUCH):** L6877, L8179, L8190
**E. AXIOM (1, UNPROVABLE):** L8830
**F. Unclassified (2):** L7971, L10077
**G. While duplication (1):** L10475

## APPROACH: Prove `convertExpr_state_determined_weak`

All category A/B/C sorries would be eliminated if you prove a WEAK version of `convertExpr_state_determined` that takes ≤ instead of =.

**Step 1**: Find `convertExpr_state_determined` with `lean_hover_info` to see its exact signature.
**Step 2**: Prove this lemma:
```lean
theorem convertExpr_state_determined_from_weak
    (e : Flat.Expr) (scope : ...) (envVar envMap : ...) (st st_a : CCState)
    (h_nextId : st_a.nextId ≤ st.nextId)
    (h_funcs : st_a.funcs.size ≤ st.funcs.size) :
    (convertExpr e scope envVar envMap st_a).fst = (convertExpr e scope envVar envMap st).fst ∧
    (convertExpr e scope envVar envMap st_a).snd.nextId = (convertExpr e scope envVar envMap st).snd.nextId ∧
    (convertExpr e scope envVar envMap st_a).snd.funcs.size = (convertExpr e scope envVar envMap st).snd.funcs.size
```
**Step 3**: If ≤ isn't enough (because `convertExpr` uses `freshVar` which reads `nextId`), you may need `=` after all. In that case, prove that the IH DOES give equality by showing `convertExpr` monotonically advances state.

## EXECUTION ORDER:
1. `lean_hover_info` on `convertExpr_state_determined` — understand what it needs
2. Pick ONE sorry pair (L7421 is mid-complexity), get goal with `lean_goal`
3. Try `lean_multi_attempt` with `["exact hAgreeOut.1", "exact hAgreeOut.1.symm", "exact (CCStateAgreeWeak.nextId_eq hAgreeOut).symm", "omega"]`
4. If none work, prove the weak version lemma

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
