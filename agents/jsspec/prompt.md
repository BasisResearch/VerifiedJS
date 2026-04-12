# jsspec — CLOSE CCExprEquiv_shifted SORRIES THEN APPLY TO CCStateAgree

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T02:05
- CC: 15 real sorries (12 original + 3 you added). Total: **63** (ANF 48 + CC 15).
- **Sorry count went UP by 21 total. CRISIS MODE. Close sorries NOW.**
- You added 3 infrastructure sorries at L1848, L1857, L1866 (convertExpr_CCExprEquiv_shifted recursive calls).
- Your own log says the fix: "replace `_ _` with explicit states in recursive IH calls."

## P0: CLOSE 3 convertExpr_CCExprEquiv_shifted SORRIES (L1848, L1857, L1866)

You already know the fix from your own analysis:
1. At each sorry, the issue is Lean can't infer implicit state args in recursive calls
2. Replace `_ _` with explicit `(Flat.convertExpr sub ... st1).snd` / `(Flat.convertExpr sub ... st2).snd`
3. Use `lean_goal` at each sorry to see the exact type expected
4. Verify each with `lean_diagnostic_messages`

**Expected: -3 sorries**

## P1: APPLY CCExprEquiv TO CLOSE CCStateAgree SORRIES (5 targets: L6865, L6891, L9777, L9854, L9970)

After P0, your convertExpr_CCExprEquiv_shifted is fully proved. Now USE it:

### For each CCStateAgree sorry:
1. The goal needs `CCStateAgree st' st_a'` or expression equality
2. Instead, provide `CCExprEquiv δ` witness where δ = `exprFuncCount` of the skipped branch
3. Use `convertExpr_state_delta` to compute δ

### BUT FIRST: Check if the simulation relation needs weakening
The current relation may require exact equality. If so, you need to change the `suffices` or `have` upstream to accept CCExprEquiv instead. This is the REAL work.

**Start with L6865** (if-true branch). Read the surrounding proof to understand what equality is actually needed.

**Expected: -2 to -5 sorries**

## P2: L9620 — Check what's needed here
`lean_goal` at L9620 to see if it's a CCStateAgree case or something else.

## DO NOT ATTEMPT:
- L8373 (getIndex semantic mismatch — UNPROVABLE)
- L6417, L7722, L7733 (multi-step architectural — different blocker)
- L7514 (check what it is but don't spend >15 min)
- Building MORE infrastructure

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — closing CCExprEquiv_shifted + applying to CCStateAgree" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
