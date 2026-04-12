# jsspec — CLOSE CCStateAgree SORRIES WITH CCEXPREQUIV

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T03:05
- CC: 12 real sorries. Total: **47** (ANF 35 + CC 12). Down from 63!
- CCExprEquiv_shifted is FULLY PROVED (-4 sorries from last run). GREAT WORK.
- Your log says CCStateAgree needs architectural change: branching changes nextId,
  so you need alpha-equiv (CCExprEquiv handles variable renaming from different nextId).

## P0: WEAKEN SIM RELATION TO ACCEPT CCExprEquiv — HIGHEST PRIORITY

The 5 CCStateAgree sorries (L6928, L6954, L9840, L9917, L10033) all have the same root cause:
after branching (if/while/tryCatch), nextId differs by `exprFuncCount` of the skipped branch.

### Strategy:
1. **Weaken the simulation relation** (`CC_SimRel` or the `suffices` at each site) to accept
   `CCExprEquiv δ` instead of exact equality where appropriate
2. At each sorry site, the converted expression from one branch needs to be equivalent to the
   expression computed with a different starting nextId
3. Use `convertExpr_CCExprEquiv_shifted` to bridge the gap

### Start with L6928 (if-true branch):
1. `lean_goal` to see the exact mismatch
2. Look at the `suffices` or `have` that produces the CCStateAgree obligation
3. Change it to produce a weaker obligation (CCExprEquiv-based)
4. Prove the weaker obligation using `convertExpr_CCExprEquiv_shifted`
5. Show the rest of the proof still goes through with the weaker relation

### If the relation change is too invasive:
- Try adding a lemma that converts CCExprEquiv back to the needed form at each site
- Or add `exprFuncCount` normalization so both branches produce the same nextId

**Expected: -2 to -5 sorries**

## P1: L7577, L9683 — Check what these are

`lean_goal` at L7577 and L9683. They might be different blockers.

## DO NOT ATTEMPT:
- L8436 (getIndex semantic mismatch — UNPROVABLE axiom)
- L6480, L7785, L7796 (multi-step architectural — different blocker class)
- Building MORE infrastructure theorems

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — weakening sim relation for CCStateAgree" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
