# jsspec — CLOSE CCStateAgreeWeak SORRIES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T13:05
- CC has **25 real sorry lines** (5 blocked/axiom, 20 CCStateAgreeWeak)
- The dominant pattern: `convertExpr_state_determined ... st_a' sorry /- hAgreeOut.1 -/ sorry /- hAgreeOut.2 -/`
- These need equality where IH only provides CCStateAgreeWeak (≤)

## THE CORE PROBLEM
`convertExpr_state_determined` requires `st_a'.nextId = st'.nextId` (equality).
But the simulation invariant at L6858-6860 only gives `CCStateAgreeWeak` (≤).
The jsspec analysis from March 31 confirmed monotone approach FAILS.

## THE FIX: CCExprEquiv-based approach

`convertExpr_CCExprEquiv_shifted` (L1854) already proves that expressions are
`CCExprEquiv δ` when states differ by δ on funcs.size. This means the EXPRESSION
part doesn't need state equality.

**Key insight**: The sorry sites use `convertExpr_state_determined` for TWO things:
1. Expression equality (`.fst`) — can be replaced with `CCExprEquiv 0` + `CCExprEquiv_refl`
2. State chaining (`.snd`) — this is the real blocker

For state chaining: prove that `convertExpr` output state delta depends ONLY on the
expression structure, not the input state values. Specifically:

```lean
theorem convertExpr_state_delta_independent (e : Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st1 st2 : Flat.CCState) :
    (Flat.convertExpr e scope envVar envMap st1).snd.nextId - st1.nextId =
    (Flat.convertExpr e scope envVar envMap st2).snd.nextId - st2.nextId ∧
    (Flat.convertExpr e scope envVar envMap st1).snd.funcs.size - st1.funcs.size =
    (Flat.convertExpr e scope envVar envMap st2).snd.funcs.size - st2.funcs.size
```

If this holds (likely — convertExpr is deterministic in its state consumption), then
from `st_a'.nextId ≤ st'.nextId` and `delta(st_a) = delta(st)`, you get equality.

## SORRY LOCATIONS (25 real sorry lines):

**A. CCStateAgreeWeak pairs (~20 lines):**
- L7181-7186 (let body), L7461 (if cond), L7610 (assign), L7868 (binary lhs)
- L7944 (call f), L8744 (getProp obj), L9038 (setProp obj), L9350 (setIndex)
- L9426 (deleteProp obj), L8145 (exprList), L9861 (propList), L10077 (arrayLit)
- L8159-8160 (hAgreeOut.symm), L9876, L10092, L10469

**B. Unclassified (2):** L8011, L10117
**C. Multi-step gap (3, BLOCKED):** L6917, L8219, L8230
**D. AXIOM (1, UNPROVABLE):** L8870
**E. While duplication (1, BLOCKED):** L10515

## EXECUTION ORDER:
1. `lean_hover_info` on `convertExpr_state_delta` at L1440 — check if delta lemma exists
2. Try proving `convertExpr_state_delta_independent` by mutual induction (same structure as `convertExpr_state_determined`)
3. If it works, derive equality from ≤ + equal deltas at each sorry site
4. Start with L7461 (if cond) — mid-complexity, single pair

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
