# jsspec — ALPHA-EQUIV CCExprEquiv FOR NEXTID SHIFTS

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T04:05
- CC: 12 real sorries. Total: **42** (ANF 30 + CC 12).
- CCExprEquiv_shifted is FULLY PROVED. GREAT WORK.
- Your 03:00 analysis confirmed: all 5 CCStateAgree sorries are ARCHITECTURALLY BLOCKED
  because branching creates nextId gaps (from freshVar in skipped branches).

## CC SORRY CLASSIFICATION (12 total):
1. **CCStateAgree (6)**: L6928, L6954, L9840, L9843, L9917, L10033 — need alpha-equiv
2. **Multi-step sim (4)**: L6480, L7577, L7785, L7796 — architectural, SKIP
3. **Axiom (1)**: L8436 — UNPROVABLE, SKIP
4. **FunctionDef (1)**: L9683 — multi-step, SKIP

## P0: EXTEND CCExprEquiv FOR NEXTID SHIFTS — ONLY PATH FORWARD

Current CCExprEquiv (L1631-1637) requires `hid : st1.nextId = st2.nextId`.
For branching, nextId differs by `exprFuncCount` of the skipped branch.

### The problem:
- `freshVar st` generates `"__cc_" ++ toString st.nextId`
- Different nextId → different generated variable names
- Need alpha-equivalence: expressions are equivalent modulo systematic renaming of generated vars

### Options (pick the most feasible):

**Option A: CCExprEquiv with nextId offset**
Extend CCExprEquiv to accept a `δ_id : Nat` offset for nextId differences:
- Generated var `"__cc_" ++ toString (base + n)` ≡ `"__cc_" ++ toString (base + δ_id + n)`
- Non-generated vars must match exactly
- This handles the systematic shift from skipped branches

**Option B: Normalize-then-compare**
Add a lemma showing `exprFuncCount` of untaken branch doesn't affect the SEMANTIC behavior:
- The funcs added by the untaken branch are never called
- The nextId shift just means different names for the same binding structure
- Prove behavioral equivalence without structural alpha-equiv

**Option C: State normalization**
Prove that you can "re-run" convertExpr with a shifted nextId and get CCExprEquiv output.
You already have `convertExpr_CCExprEquiv_shifted` for equal nextId — extend to shifted nextId.

### Start by:
1. `lean_goal` at L6928 to see the exact gap between `st` and `st_a`
2. Determine which of nextId, funcs.size, or both differ
3. Pick the minimal extension that bridges the gap
4. Implement and test on L6928 first, then apply to other 5 sites

**Expected: -2 to -6 sorries if successful**

## DO NOT ATTEMPT:
- L8436 (getIndex semantic mismatch — UNPROVABLE)
- L6480, L7577, L7785, L7796 (multi-step — different blocker class entirely)
- Building more infrastructure theorems without applying them

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — alpha-equiv CCExprEquiv" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
