# jsspec — CC SORRY ANALYSIS + TARGETED CLOSURES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T18:05
- CC has **~24 sorry occurrences** on ~20 lines
- Sandwich argument PROVEN INFEASIBLE (good analysis, documented)
- CCExprEquiv Approach B is DEAD (δ-consistency flaw)
- 5 blocked/axiom sorries (L6917, L8235, L8246, L8889, L10544) — DO NOT TOUCH

## CRITICAL: THE SANDWICH IS DEAD. NEW DIRECTION NEEDED.

You correctly proved the sandwich argument wrong: `st_a'` comes from STEPPED expression, not original, so `exprFuncCount` differs after branching reductions.

### NEW APPROACH: CASE-BY-CASE exprFuncCount ANALYSIS

The sandwich fails ONLY when `exprFuncCount` changes through a Core step. But NOT all Core steps change it!

**Key insight**: For SOME sorry sites, the Core step does NOT involve branching, so `exprFuncCount` IS preserved, and the sandwich DOES work locally.

**Your task**: For EACH of the 9 funcs.size sorry sites, check:
1. What Core step constructor is being handled at that sorry site?
2. Does that step constructor preserve `exprFuncCount`?
3. If YES → apply the sandwich argument locally
4. If NO → mark as architecturally blocked

### Specific sites to investigate:
- **L7619 (seq substep)**: seq step goes from `.seq a b` to `.seq a' b`. Does `exprFuncCount (.seq a b) = exprFuncCount (.seq a' b)` hold when `Core.Step (.seq a b) ev (.seq a' b)`? If the step is in `a` and `a` doesn't branch, YES.
- **L7880 (binary lhs)**: Similar — binary step in lhs, no branching
- **L7959 (call f)**: Step in function expression before call — might not branch
- **L7184 (let body)**: After let binding — check if this involves branching
- **L7466 (if cond)**: Step in condition — probably doesn't branch (branching happens at if-value)

For each, use `lean_goal` to see the exact Core step being handled and check if `exprFuncCount` is preserved.

### If that yields nothing:
Investigate weakening the CC_SimRel invariant:
- Can `CCStateAgree` be weakened from `funcs.size =` to `funcs.size ≤` + a weaker expression relation?
- Look at WHERE funcs.size equality is actually USED downstream (not just asserted)
- If it's only used in `makeClosure` index computation, perhaps indices can be made relative

### SORRY LOCATIONS (24 occurrences, ~20 lines):

**A. funcs.size equality (9 lines):** L7184, L7466, L7619, L7880, L7959, L8762, L9059, L9374, L9453
**B. List hAgreeIn (3 lines, 6 occ):** L8161, L9890, L10106
**C. hAgreeOut.symm (5 lines):** L8175, L8176, L9905, L10121, L10498
**D. Unclassified (2):** L8027, L10146
**E. BLOCKED (3):** L6917, L8235, L8246
**F. AXIOM (1):** L8889
**G. While dup (1):** L10544

## EXECUTION ORDER:
1. `lean_goal` at L7619 — check if seq step preserves exprFuncCount
2. `lean_goal` at L7466 — check if cond step preserves exprFuncCount
3. For any that DO preserve: apply sandwich locally
4. Document which sites are truly blocked vs closable
5. If nothing closable: investigate weakening CC_SimRel

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
