# jsspec — CLOSE CCStateAgree SORRIES (L5491 + L5517 first)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 15 CC sorries remain. Total: 51.
- CC_SimRel error disjunct: DONE (3 error sites filled, 3 tryCatch-init edge cases added)
- The 3 new tryCatch-init sorries (L5265, L5409, L5696) are BLOCKED by L8484
- All multi-step sorries (L5044, L6139, L6347, L6358) are BLOCKED
- L6998 is UNPROVABLE
- L8250 (functionDef) is BLOCKED (multi-step + complex)

## SORRY CLASSIFICATION (15 total)
- CCStateAgree: 5 (L5491, L5517, L8407, L8484, L8600) ← YOUR TARGET
- TryCatch-init edge: 3 (L5265, L5409, L5696) — blocked by L8484
- Multi-step: 3 (L5044, L6347, L6358)
- Non-consoleLog call: 1 (L6139) — multi-step
- Unprovable: 1 (L6998)
- functionDef: 1 (L8250)
- tryCatch finally: 1 (L8410)

## P0: CCStateAgree AT L5491 AND L5517

### What CCStateAgree is
```lean
private abbrev CCStateAgree (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId = st2.nextId ∧ st1.funcs.size = st2.funcs.size
```

### The problem at L5491 (if_branch, else case)
After stepping the condition sub-expression, the suffices needs `CCStateAgree st st_a` where:
- `st` = the state BEFORE converting the full if-expression
- `st_a` = some state that makes `(sf'.expr, st_a') = Flat.convertExpr sc'.expr ...`

The issue: `convertExpr (.if cond then_ else_)` converts `cond`, `then_`, `else_` sequentially. After cond steps, the remaining expression (`.if cond' then_ else_`) needs conversion starting from a state that accounts for what cond consumed. But the IH gives a state from converting only cond.

### APPROACH: Use convertExpr_state_determined (L570)
The theorem `convertExpr_state_determined` (L570-574) proves:
```
If st1.nextId = st2.nextId ∧ st1.funcs.size = st2.funcs.size, then
convertExpr e ... st1 = convertExpr e ... st2 (same output expression and state agreement)
```

This means if you can show `CCStateAgree st st_a`, the conversion output is the same regardless of other CCState fields.

**STEP BY STEP**:
1. Run `lean_goal` at L5491 to see the exact proof state
2. Identify what `st_a` needs to satisfy
3. The key: after stepping `cond` (via IH), the IH gives back `CCStateAgree st' st_a'` for the output state. The INPUT state `st_a` should be constructible from `st` + the fact that stepping doesn't change CCState.
4. Core.step? does NOT modify `CCState` — it's a compile-time artifact. So `st_a = st` should work!

**CHECK**: Does the IH destructuring at the sorry site give you `CCStateAgree` for the sub-expression? If so, you can thread it through using `convertExpr_state_determined`.

## P1: L5517 (similar CCStateAgree, if_branch then case)

Same approach. After understanding L5491, apply the pattern.

## P2: IF P0/P1 CLOSED — TRY L8407

L8407 is `by rw [hst'_eq]; sorry` in a tryCatch case. Run `lean_goal` to see what's needed after the rewrite.

## SKIP (DO NOT ATTEMPT):
- Multi-step (L5044, L6139, L6347, L6358): needs N-step simulation
- L6998: UNPROVABLE semantic mismatch
- L8250: functionDef, too complex
- L8410, L8600: need deeper CCStateAgree + tryCatch/while infrastructure
- L5265, L5409, L5696: blocked by L8484

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgree L5491 + L5517" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
