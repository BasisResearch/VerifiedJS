# proof — Restore CC step_sim proof (L945)

## Build ONLY your module
```
bash scripts/lake_build_concise.sh VerifiedJS.Proofs.ClosureConvertCorrect
```

## Use MCP BEFORE editing
- lean_goal to see state
- lean_multi_attempt to test tactics
- lean_diagnostic_messages for errors

## TASK: Replace `exact sorry` at L945 with case analysis

### Context
At L945, `exact sorry` covers the ENTIRE `closureConvert_step_simulation` inner induction.

The suffices block (L915-937) is correct. The intro at L941:
```lean
intro envVar envMap injMap sf sc ev sf' hd htrace hinj henvCorr henvwf hheapvwf hncfr hexprwf ⟨scope, st, st', hconv⟩ ⟨hstep⟩
```

**KEY**: HeapInj and EnvCorrInj are ALIASES (L650, L655):
```lean
private def HeapInj (_injMap : Nat → Nat) (ch fh : Core.Heap) : Prop := HeapCorr ch fh
private def EnvCorrInj (_injMap : Nat → Nat) (cenv : Core.Env) (fenv : Flat.Env) : Prop := EnvCorr cenv fenv
```

`injMap` is IGNORED everywhere. Always output `injMap` unchanged.

### Step 1: Replace `exact sorry` at L945 with this skeleton

```lean
  -- hstep : Flat.step? sf = some (ev, sf') (from Flat.Step)
  -- hconv : (sf.expr, st') = Flat.convertExpr sc.expr scope envVar envMap st
  -- Case-split on sc.expr to determine sf.expr via convertExpr
  -- Then unfold Flat.step? to analyze the step, construct Core.step? result
  -- Use convertExpr to relate expressions, use HeapCorr/EnvCorr to transfer values

  -- Start: determine sf.expr from hconv
  cases hsc : sc.expr with
  | lit v =>
    -- convertExpr (.lit v) = .lit (convertValue v), so sf.expr = .lit (convertValue v)
    -- But Flat.step? of .lit is none → contradicts hstep
    simp [Flat.convertExpr] at hconv
    obtain ⟨hfexpr, _⟩ := hconv
    rw [← hfexpr] at hstep
    simp [Flat.Step] at hstep
    -- If that doesn't close it, try:
    -- have : Flat.step? sf = none := by simp [Flat.step?, hfexpr ▸ rfl]
    -- exact absurd hstep (by simp [this])
    sorry
  | var name => sorry
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

### Step 2: Close the `.lit` case (contradiction)
The lit case should be a contradiction: `Flat.step?` on a literal returns `none`, but `hstep` says it returned `some`. Use `lean_goal` at the sorry to see the exact state, then close it.

### Step 3: Close easy cases
After `.lit`, try `.var`, `.this`, `.return`, `.typeof`. Pattern:
1. Unfold `convertExpr` in `hconv` to get `sf.expr`
2. Unfold `Flat.step?` to compute the Flat step
3. Construct the Core step: `⟨sc', Core.step? sc = some (ev, sc')⟩`
4. Output: `⟨injMap, sc', ⟨hcstep⟩, htrace', hinj, henvCorr, henvwf', hheapvwf, hncfr', hexprwf', ...⟩`

For `injMap'`, ALWAYS use `injMap` (since HeapInj ignores it).

### What NOT to do
- Do NOT change HeapInj/EnvCorrInj definitions
- Do NOT change CC_SimRel structure
- Do NOT change any file outside ClosureConvertCorrect.lean
- Do NOT touch ANF or Wasm files
- Do NOT try to prove ALL cases — close what you can, leave rest as sorry

## Log progress to agents/proof/log.md
