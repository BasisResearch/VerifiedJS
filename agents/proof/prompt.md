# proof — Restore CC step_sim proof (L945)

## Build ONLY your module
```
bash scripts/lake_build_concise.sh VerifiedJS.Proofs.ClosureConvertCorrect
```

## Use MCP BEFORE editing
- lean_goal to see state
- lean_multi_attempt to test tactics
- lean_diagnostic_messages for errors

## TASK: Restore the CC step_sim proof at ClosureConvertCorrect.lean L945

### Context
The sorry at L945 (`exact sorry`) covers the ENTIRE `closureConvert_step_simulation` inner induction. The `suffices` block (L915-937) already has the correct signature with injMap threading. The intro at L941 destructs `hstep` into `⟨hstep⟩`.

**KEY INSIGHT**: `HeapInj` and `EnvCorrInj` are currently ALIASES:
```lean
-- L650:
private def HeapInj (_injMap : Nat → Nat) (ch fh : Core.Heap) : Prop := HeapCorr ch fh
-- L655:
private def EnvCorrInj (_injMap : Nat → Nat) (cenv : Core.Env) (fenv : Flat.Env) : Prop := EnvCorr cenv fenv
```

This means `injMap` is IGNORED. You can always use the SAME injMap in the output. The proof is structurally identical to a proof that uses `HeapCorr` and `EnvCorr` directly.

### Strategy
Replace `exact sorry` at L945 with case analysis on `Flat.step?`:

```lean
  -- The step destructs to: Flat.step? sf = some (ev, sf')
  -- Case-split on sf.expr (which determines what Flat.step? does)
  -- For each case, find the corresponding Core.step? result
  -- Use hconv to relate sf.expr to convertExpr sc.expr
  -- Use hinj/henvCorr to transfer values

  -- Start with the easiest cases first:
  simp [Flat.step?, Flat.exprValue?] at hstep
  -- Then split on sc.expr (since sf.expr = convertExpr sc.expr ...)
  obtain ⟨scope, st, st', hconv⟩ := ⟨scope, st, st', hconv⟩
  cases sc.expr with
  | lit v =>
    -- convertExpr (.lit v) = (.lit (convertValue v), st)
    -- Flat.step? of .lit is none → contradiction with hstep
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, _⟩ := hconv
    rw [hfexpr] at hstep
    simp [Flat.step?, Flat.exprValue?] at hstep
  | var name =>
    -- convertExpr (.var name) produces .getEnv or .var depending on scope
    sorry
  | «this» => sorry
  | «let» name init body => sorry
  | assign name rhs => sorry
  | «if» cond then_ else_ => sorry
  | seq a b => sorry
  | unary op arg => sorry
  | binary op lhs rhs => sorry
  | call f args => sorry
  | «return» val => sorry
  | throw val => sorry
  | tryCatch body name handler => sorry
  | typeof arg => sorry
  | _ => sorry  -- remaining cases
```

### Approach for each case
1. Use `hconv` to determine `sf.expr` from `convertExpr sc.expr`
2. Unfold `Flat.step?` to see what the Flat side does
3. Construct matching `Core.step?` result
4. Build output with `⟨injMap, sc', hcstep, htrace', hinj, henvCorr, ...⟩`
5. For `injMap'`, just use the same `injMap` (since HeapInj ignores it)

### Priority
1. Replace `exact sorry` with the `cases sc.expr` skeleton above
2. Close the `.lit` case (contradiction — should be easy)
3. Close 2-3 simple value cases (.var in scope, .this, .seq with value)
4. Leave complex cases (call, tryCatch) as sorry
5. Do NOT touch ANF or Wasm files

### What NOT to do
- Do NOT try to implement "real" HeapInj — just use the alias
- Do NOT restructure CC_SimRel
- Do NOT change any file outside ClosureConvertCorrect.lean

## Log progress to agents/proof/log.md
