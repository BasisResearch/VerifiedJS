# jsspec — hasAbruptCompletion_step_preserved (L13922) + error cases

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 23 sorries. ANF: 42. Total: 65.
- Last jsspec run: 2026-03-31. 11 DAYS AGO.
- Error propagation IS DONE in Flat/Semantics.lean.
- All CC sorries thoroughly assessed. Most architecturally blocked.

## ALL 23 CC SORRIES — CATEGORIZED:

**Closable (potentially):**
- L1469 + L1473 — closConvertExpr_state_mono (2 sorries)
- L5116, L5215, L5454 — error-case sorries, may be closable with error propagation

**CCStateAgree (architecturally blocked, 6):**
- L5297, L5323, L8169, L8172, L8246, L8362

**Multi-step (architecturally blocked, 3):**
- L4949, L6108, L6119

**Other blocked:**
- L5900 — functionDef
- L6759 — getIndex string (UNPROVABLE — semantic mismatch)
- L8012 — tryCatch

## P0: FIX hasAbruptCompletion_step_preserved (L13922 in ANFConvertCorrect.lean)

Wait — you DON'T own ANFConvertCorrect.lean. Skip this.

## P0 (REVISED): CLOSE L1469 + L1473 (closConvertExpr_state_mono)

These are about monotonicity of closure conversion state (nextId only increases).

1. `lean_goal` at L1469 to see what's needed
2. `lean_goal` at L1473 to see the main sorry
3. This should be provable by induction on the expression — each case of `convertExpr` either calls `freshVar` (incrementing nextId) or threads state through sub-expressions
4. `lean_local_search "convertExpr_state"` to see related lemmas
5. Try `lean_multi_attempt` at L1473 with: `["induction e", "cases e"]`

## P1: RE-ASSESS ERROR CASES (L5116, L5215, L5454)

Error propagation IS DONE. Check if these are now closable:
1. `lean_goal` at each
2. `lean_multi_attempt` with simple tactics
3. The key change: when a sub-expression steps with `.error msg`, the compound wrapper is dropped

## P2: COMMENT CLEANUP

Update "BLOCKED" comments with accurate status. Delete outdated comments about error propagation not being done.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — state_mono L1469 L1473" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
