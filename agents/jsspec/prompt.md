# jsspec — CCExprEquiv OFFSET THEOREM + INVARIANT REFACTOR

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T23:30
- CC: 12 real sorries. Total: **42** (ANF 30 + CC 12). Down from 44 (-2).
- CCExprEquiv defined with δ parameter. Proved: refl, eq_implies_zero, of_agree.
- noFunctionDef CANNOT close any sorry (supported allows functionDef). CONFIRMED.
- Next step: `convertExpr_CCExprEquiv_offset` theorem.

## P0: PROVE convertExpr_CCExprEquiv_offset (HIGHEST PRIORITY)

This is the KEY theorem that enables closing CCStateAgree sorries.

Statement:
```lean
theorem convertExpr_CCExprEquiv_offset (e : Core.Expr) (st1 st2 : CCState)
    (h_agree : st1.nextId = st2.nextId) (h_funcs : st1.funcs.size = st2.funcs.size) :
    CCExprEquiv (st2.funcs.size - st1.funcs.size)
      (convertExpr e st1).fst (convertExpr e st2).fst
```

i.e., converting the SAME expression from two states that agree on nextId and funcs.size produces CCExprEquiv expressions with δ = funcs.size difference.

When `st1 = st2`, this gives CCExprEquiv 0, which you already have.
When st1 and st2 differ (e.g., st2 has extra funcs from discarded branch), δ accounts for the offset in makeClosure indices.

### Proof strategy:
1. Mutual structural induction on `e` (like `convertExpr_state_delta`)
2. Most cases: sub-expression results are CCExprEquiv by IH, constructor preserves it
3. `functionDef` case: `addFunc` increments funcs.size → δ shifts by 1 → makeClosure index offset
4. The δ parameter absorbs the state difference

### How it closes sorries:
For L6576 (if-true CCStateAgree): `st' = (convertExpr else_ (convertExpr then_ st).snd).snd` but we only took the then_ branch. With CCExprEquiv, we show the then_ expression from `st'` is CCExprEquiv δ to the then_ expression from `(convertExpr then_ st).snd`. The simulation invariant accepts CCExprEquiv instead of equality.

## P1: REFACTOR SIMULATION INVARIANT (only after P0 done)

Change the simulation invariant from `CCStateAgree` (equality) to:
```lean
structure CCSimRel (sf : Flat.State) (sc : Core.State) : Prop where
  expr_equiv : CCExprEquiv δ sf.expr sc.expr  -- instead of equality
  state_agree_weak : sc.nextId ≤ sf.nextId    -- instead of equality
  -- ... other fields
```

This is a MAJOR refactor. Only start if P0 is fully proved and verified.

### Priority CCStateAgree sorries (5):
- L6576, L6602: if-branch (then/else CCStateAgree)
- L9488, L9565: CCStateAgree after sub-expression
- L9681: while_ CCStateAgree

## DO NOT ATTEMPT:
- Multi-step simulation sorries (L6128, L7433, L7444) — different blocker
- L8084 (getIndex semantic mismatch — unprovable)
- L7225, L9331, L9491 — dependent on other infrastructure

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCExprEquiv offset theorem" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
