# jsspec — Close CC value sub-cases (wasmspec is STUCK, you take over)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap.

## STATE (05:05): CC has 17 sorries, build PASSES

## CRITICAL CHANGE: CCStateAgree sorries are CONFIRMED BLOCKED
Your analysis in the 03:00 and 04:00 runs was correct:
- L2933, L3252, L3274, L5313 are architecturally impossible with current invariant
- The monotone approach breaks chaining (you proved this)
- Path A (state-independent conversion) requires editing ClosureConvert.lean (read-only for you)
- **DO NOT work on these 4 sorries. They need definition changes.**

## NEW MISSION: Take over wasmspec's value sub-cases
wasmspec has been STUCK in a while loop for 15+ hours. You now own its targets.

### YOUR TARGETS (7 sorries):
1. **L4831 — objectLit all-values** (EASIEST, start here)
2. **L5014 — arrayLit all-values** (same pattern as objectLit)
3. **L4509 — setIndex value sub-case**
4. **L3768 — call callee-is-value**
5. **L3769 — newObj**
6. **L5192 — functionDef**
7. **L5282 — tryCatch** (hardest, skip if short on time)

### HOW TO PROVE objectLit all-values (L4831):

Context: `Core.firstNonValueProp props = none` means ALL props are `.lit _`.

Key facts in scope at L4831:
- `hcfnv : Core.firstNonValueProp props = none`
- `hfexpr : sf.expr = Flat.Expr.objectLit (Flat.convertPropList props scope envVar envMap st).fst`
- `hconv : (sf.expr, st') = Flat.convertExpr (.objectLit props) scope envVar envMap st`
- `hstep : Flat.step? sf = some (ev, sf')`

The proof pattern (follow getProp value case at L3776-3867 for reference):
1. When all props are values, `convertPropList` maps `(k, .lit v)` → `(k, .lit (convertValue v))`
2. Flat.step? on objectLit with all-value props allocates a new heap object
3. Core.step? on objectLit with all-value props also allocates a new heap object
4. HeapInj extends naturally (both add one object at the end)
5. CCState is unchanged (no freshVar/addFunc in value conversion)

Try this approach:
```lean
-- First check what Flat.step? does with all-value objectLit
have hall : Flat.valuesFromPropList? (Flat.convertPropList props scope envVar envMap st).fst = some _ := by
  sorry -- need to show all converted props are values
-- Then unfold the step
simp [Flat.step?, hfexpr, hall] at hstep
```

Use `lean_goal` at L4831 to see the exact goal. The LSP takes ~3 minutes on this file — just
run the command and WAIT. Do NOT use any loop to poll for results.

### HOW TO PROVE arrayLit all-values (L5014):
Identical pattern to objectLit but with `firstNonValueExpr` and `valuesFromExprList?`.

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
- CCState threading sorries (L2933, L3252, L3274, L5313) — architecturally blocked

## WORKFLOW:
1. `lean_goal` at L4831 → read FULL goal (wait for LSP, ~3 min)
2. Study nearby proved cases (getProp at L3776, setProp, deleteProp) for patterns
3. Build the proof step by step
4. Build after every successful change
5. Move to next target

## CRITICAL: YOU MUST LOG WHAT YOU DO
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run — value sub-cases" >> agents/jsspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`

## TARGET: Close at least 2 of 7 value sub-cases → CC from 17 to ~15
