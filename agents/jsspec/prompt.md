# jsspec — CCStateAgree: GLOBAL INVARIANT CHANGE

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T06:05
- CC: **12** real sorries. Total: **42** (ANF 30 + CC 12).
- convertExpr_expr_eq_of_funcs_size infrastructure DONE.
- CCStateAgree analysis complete: global invariant change IS needed.

## YOUR ANALYSIS CONCLUSION (from last run):
You correctly identified:
1. Branching creates a gap in BOTH nextId AND funcs.size
2. No local fix works — the simulation invariant itself needs changing
3. Need CCExprEquiv δ instead of exact equality

## THE PATH FORWARD: WEAKEN THE INVARIANT INCREMENTALLY

The suffices block (L6411-6413) currently requires:
```lean
(sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
CCStateAgree st st_a ∧ CCStateAgree st' st_a'
```

**Option A (RECOMMENDED — smallest change):** Instead of exact equality for expr, use:
```lean
∃ δ, (sf'.expr = (Flat.convertExpr sc'.expr scope envVar envMap (st_a.withFuncsSize (st_a.funcs.size + δ))).fst) ∧
  st_a'.funcs.size = (Flat.convertExpr sc'.expr scope envVar envMap (st_a.withFuncsSize (st_a.funcs.size + δ))).snd.funcs.size
```
Then use `convertExpr_expr_eq_of_funcs_size` to show that δ doesn't affect expr equality when funcs.size is aligned.

Wait — you already showed expr depends on funcs.size too. So actually:

**Option B (ACTUALLY correct):** The real insight is that after branching, the expressions
produced are IDENTICAL because they don't depend on nextId at all (only funcs.size matters),
AND funcs.size is deterministic. So the only difference is in `nextId`. Define:
```lean
def CCStateAgreeWeak (st_real st_sim : CCState) : Prop :=
  st_real.funcs.size = st_sim.funcs.size
  -- (nextId can differ)
```

**Option C (HYBRID):** Keep CCStateAgree for funcs agreement, allow nextId to differ:
```lean
def CCStateAgreeModNextId (st_real st_sim : CCState) : Prop :=
  st_real.funcs = st_sim.funcs ∧ st_real.names = st_sim.names
  -- nextId can differ
```

**START HERE:**
1. `lean_goal` at L7136 and L10241 to see the EXACT mismatch
2. Determine which fields actually MUST agree vs which can differ
3. If only nextId differs: Option C is cleanest — just weaken CCStateAgree to drop nextId
4. Test on ONE sorry first before changing the invariant globally

## DO NOT TOUCH:
- L6688, L7993, L8004 (multi-step — architectural, different class)
- L7785 (unclassified)
- L8644 (getIndex — UNPROVABLE)
- L9891 (functionDef — multi-step)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgree invariant weakening" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
