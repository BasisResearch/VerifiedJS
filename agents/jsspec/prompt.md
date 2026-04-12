# jsspec — ALPHA-EQUIV CCExprEquiv FOR NEXTID SHIFTS

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T05:05
- CC: **12** real sorries. Total: **43** (ANF 31 + CC 12).
- Down from 63 last run (-20). CCExprEquiv_shifted is DONE.
- 6 CCStateAgree sorries are the MAIN target.

## CC SORRY MAP (12 total):

**P0: CCStateAgree (6 sorries) — YOUR ONLY FOCUS:**
- L6918 (if-true CCStateAgree) — st' includes else_ conversion but sim follows then_ only
- L6944 (if-false CCStateAgree) — st' includes then_ conversion but sim follows else_ only
- L9830 (tryCatch body-value) — CCStateAgree after body steps
- L9833 (tryCatch body-value + finally) — same class
- L9907 (tryCatch throw CCStateAgree) — state after catch conversion
- L10023 (while_ CCStateAgree) — duplicated sub-expression conversion

**Root cause**: `freshVar st` generates `"__cc_" ++ toString st.nextId`. When branches
are skipped, nextId advances by `exprFuncCount` of the skipped branch. The converted
expressions differ only in generated variable names (systematic offset).

**Strategy**: You need ONE of:
1. **Alpha-equiv with offset**: Extend CCExprEquiv to handle `δ_id` offset between
   generated variable names. Show that behavioral equivalence holds under renaming.
2. **Semantic irrelevance**: Prove that the funcs/names added by untaken branches are
   never referenced during execution. The state difference is "dead" state.
3. **convertExpr determinism mod offset**: Show convertExpr with shifted input state
   produces alpha-equivalent output.

**Start with**: `lean_goal` at L6918 to see the EXACT mismatch. Then pick the minimal fix.

**DO NOT TOUCH:**
- L6470, L7775, L7786 (multi-step simulation — architectural, different class)
- L7567 (unclassified — investigate only if everything else done)
- L8426 (getIndex semantic mismatch — UNPROVABLE)
- L9673 (functionDef — multi-step)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — alpha-equiv for CCStateAgree" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
