# jsspec — CLOSE FuncsCorr INIT (L1519) + ERROR CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — FuncsCorr BULK CLOSE DONE!
- The 72 FuncsCorr sorry⟩ bulk close worked! Only 2 sorry⟩ remain (L5333, L8201).
- CC now has **16 real sorries**. Total project: 46.
- Excellent work on the bulk close.

## P0: CLOSE L1519 (FuncsCorr initial state)

This is the FuncsCorr for the initial CC_SimRel. Run `lean_goal` at L1519.

Context (L1510-1519):
```lean
unfold CC_SimRel Flat.initialState Core.initialState
refine ⟨rfl, ⟨id, HeapInj_id _, ?_, ?funcCorr_init⟩, h_wf, ...⟩
case funcCorr_init =>
  -- FuncsCorr for initial state: Core has [logBuiltin], Flat has t.functions
  sorry
```

**APPROACH**:
1. Run `lean_goal` at L1519 to see the exact goal
2. FuncsCorr relates Core funcs and Flat funcs through injMap. Initial Core funcs = `#[logBuiltin]` (from elaborate). Initial Flat funcs = `t.functions` (from closureConvert).
3. `closureConvert` adds the console.log builtin as the first function. Check if `t.functions` at init = `#[flatLogBuiltin]` or similar.
4. With `injMap = id`, FuncsCorr should require that for each Core func at index i, Flat has a matching func at index id(i) = i.
5. Try: `unfold FuncsCorr; intro i fi hfi; ...` then case split on the single function.

## P1: ERROR STRUCTURAL MISMATCH (L5152, L5251, L5490)

These say "Flat.step? drops the .let wrapper on error but Core.step? keeps it". Run `lean_goal` at each.

**Key insight**: On error, Flat produces `sa.expr = error_result` (no .let wrapper) while Core produces `sc'.expr = .let name error_result body`. The SimRel needs `convertExpr sc'.expr = sf'.expr`. But `convertExpr (.let name err body) = .let name (convertExpr err) (convertExpr body)` ≠ `error_result`.

If this is truly a structural mismatch, it may need a SimRel adjustment (error states don't need expression matching). **Investigate first** — run lean_goal and check if there's a way around it.

## P2: L5933 (call case, non-consoleLog)

FuncsCorr is now available in scope. The comment says "needs multi-step simulation (Flat call is N steps vs Core's 1)". Run `lean_goal` to check if this is truly multi-step blocked or if it's now partially provable with FuncsCorr.

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5333, L5359, L8201, L8204, L8278, L8394: CCStateAgree (6 total)
- L4984, L6141, L6152: multi-step simulation gap (3 total)
- L6792: semantic mismatch (UNPROVABLE)
- L8044: functionDef (multi-step + FuncsCorr maintenance)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr init L1519" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
