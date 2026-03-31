# jsspec — Close CC value sub-cases (wasmspec is STUCK, you take over)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap.

## STATE (06:05): CC has 17 sorries, build PASSES. File is 6464 lines.

## SORRY LOCATIONS (UPDATED — line numbers shifted!)
```
L1520  forIn stub (SKIP — unprovable)
L1521  forOf stub (SKIP — unprovable)
L2960  HeapInj refactor staging (SKIP)
L3279  CCStateAgree if-then (SKIP — blocked)
L3301  CCStateAgree if-else x2 (SKIP — blocked)
L3807  call callee-is-value ← YOUR TARGET
L3918  newObj ← YOUR TARGET
L4486  getIndex string value mismatch (SKIP — Flat/Core semantic mismatch)
L4658  setIndex value sub-case ← YOUR TARGET
L4980  objectLit all-values ← YOUR TARGET (EASIEST)
L5163  arrayLit all-values ← YOUR TARGET
L5341  functionDef ← YOUR TARGET
L5431  tryCatch ← YOUR TARGET (hardest)
L5462  CCState threading while_ (SKIP — blocked)
```

## YOUR PROVABLE TARGETS (7 sorries):
1. **L4980 — objectLit all-values** (EASIEST, start here)
2. **L5163 — arrayLit all-values** (same pattern as objectLit)
3. **L4658 — setIndex value sub-case**
4. **L3807 — call callee-is-value**
5. **L3918 — newObj**
6. **L5341 — functionDef**
7. **L5431 — tryCatch** (hardest, skip if short on time)

### HOW TO PROVE objectLit all-values (L4980):

Context: `Core.firstNonValueProp props = none` means ALL props are `.lit _`.

Key facts in scope:
- `hcfnv : Core.firstNonValueProp props = none`
- `hfexpr : sf.expr = Flat.Expr.objectLit (Flat.convertPropList props scope envVar envMap st).fst`
- `hconv` and `hstep` from parent

The proof pattern (follow getProp value case at L3919-3939 for reference):
1. When all props are values, `convertPropList` maps `(k, .lit v)` → `(k, .lit (convertValue v))`
2. Flat.step? on objectLit with all-value props allocates a new heap object
3. Core.step? on objectLit with all-value props also allocates a new heap object
4. HeapInj extends naturally (both add one object at the end)
5. CCState is unchanged (no freshVar/addFunc in value conversion)

Use `lean_goal` at L4980 to see the exact goal. LSP takes ~3 minutes — just WAIT.

### TACTIC PATTERNS (from proved cases nearby):
```lean
-- For getting the literal form:
have hlit : obj = .lit cv := by
  cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
subst hlit
simp [Flat.convertExpr] at hfexpr hst

-- For sf eta:
have hsf_eta : sf = { sf with expr := ... } := by cases sf; simp_all

-- For constructing the result:
refine ⟨injMap', { sc with ... }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, st, st', ?_, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
```

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf stubs (L1520-1521) — unprovable
- CCState threading sorries (L3279, L3301, L5462) — architecturally blocked
- getIndex string mismatch (L4486) — Flat/Core semantic mismatch

## WORKFLOW:
1. `lean_goal` at target line → read FULL goal (wait for LSP, ~3 min)
2. Study nearby proved cases (getProp at L3919, setProp, deleteProp) for patterns
3. Build the proof step by step
4. Build after every successful change
5. Move to next target

## CRITICAL: YOU MUST LOG WHAT YOU DO
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run — value sub-cases" >> agents/jsspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`

## TARGET: Close at least 2 of 7 value sub-cases → CC from 17 to ~15
