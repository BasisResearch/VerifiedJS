# jsspec — Close CC value sub-cases (you are the ONLY productive agent right now)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE (07:00): CC has 20 grep-sorry hits, build PASSES. File is ~6460 lines.
- You added L2035 and L2048 helper lemmas (sorry'd) in your 05:00 session. Good scaffolding.
- proof and wasmspec are STUCK (while loops). You're the only one making progress.

## SORRY MAP (current grep -n sorry output):
```
L1520  forIn stub (SKIP — unprovable)
L1521  forOf stub (SKIP — unprovable)
L2035  Flat_step?_call_arg_step helper (YOUR scaffolding — close when working on call)
L2048  Flat_step?_call_nonclosure helper (YOUR scaffolding — close when working on call)
L2960  HeapInj refactor staging (SKIP)
L3279  CCStateAgree if-then (SKIP — blocked)
L3301  CCStateAgree if-else x2 (SKIP — blocked)
L3803  call all-values ← YOUR TARGET
L3805  call non-value arg ← YOUR TARGET
L3806  newObj ← YOUR TARGET
L4374  getIndex string value mismatch (SKIP — Flat/Core semantic mismatch)
L4546  setIndex value sub-case ← YOUR TARGET
L4868  objectLit all-values ← YOUR TARGET (EASIEST)
L5051  arrayLit all-values ← YOUR TARGET
L5229  functionDef ← YOUR TARGET
L5319  tryCatch ← YOUR TARGET (hardest)
L5350  CCState threading while_ (SKIP — blocked)
```

## YOUR PROVABLE TARGETS (9 sorries including your 2 helpers):
1. **L4868 — objectLit all-values** (EASIEST, start here)
2. **L5051 — arrayLit all-values** (same pattern as objectLit)
3. **L4546 — setIndex value sub-case**
4. **L2035 — Flat_step?_call_arg_step** (your helper, close by unfolding Flat.step?)
5. **L2048 — Flat_step?_call_nonclosure** (your helper, close remaining cases)
6. **L3803 — call callee-is-value** (uses L2035+L2048)
7. **L3805 — call non-value arg**
8. **L3806 — newObj**
9. **L5229 — functionDef**
10. **L5319 — tryCatch** (hardest, skip if short on time)

### HOW TO PROVE objectLit all-values (L4868):

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

Use `lean_goal` at L4868 to see the exact goal. LSP takes ~3 minutes — just WAIT.

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

### HOW TO CLOSE L2035 (Flat_step?_call_arg_step):
This is a helper lemma about Flat.step? on a call with a non-value arg.
```lean
-- Try: unfold Flat.step?, use hvals (valuesFromExprList? = none) and hfnv (firstNonValueExpr)
simp [Flat.step?, hvals, hfnv, hss, Flat.pushTrace]
```

### HOW TO CLOSE L2048 (Flat_step?_call_nonclosure non-closure cases):
Each `fv` case that isn't `.closure` should reduce:
```lean
-- Try: simp [Flat.step?, hvals, Flat.pushTrace]
```

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf stubs (L1520-1521) — unprovable
- CCState threading sorries (L3279, L3301, L5350) — architecturally blocked
- getIndex string mismatch (L4374) — Flat/Core semantic mismatch

## WORKFLOW:
1. `lean_goal` at target line → read FULL goal (wait for LSP, ~3 min)
2. Study nearby proved cases (getProp at L3919, setProp, deleteProp) for patterns
3. Build the proof step by step
4. Build after every successful change
5. Move to next target

## CRITICAL: YOU MUST LOG WHAT YOU DO
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run — value sub-cases" >> agents/jsspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`

## TARGET: Close at least 3 of 10 provable sorries → CC grep from 20 to ~17 or less
