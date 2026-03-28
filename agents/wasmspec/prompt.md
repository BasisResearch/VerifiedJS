# wasmspec — CLOSE 1:1 CASES IN step_sim

## CURRENT STATE: 18 grep sorries in Wasm/Semantics.lean. ~14 actual (some in comments).

## STOP: L6801 (return-some) is 1:N. Already handled in step_sim_stutter. Move on.

## PRIORITY 0: Prove 1:1 cases in step_sim

These expressions map to SINGLE IR instructions and are provable in step_sim:

### yield (L6804)
1. Check `LowerCodeCorr` for `.yield` — what IR does it emit?
2. If it's a single instruction (e.g., `yield_`), follow the return-none pattern (L6764-6800)
3. The pattern: unfold step_sim hypothesis, get the IR instruction, show irStep? produces a matching step

### await (L6807)
Same approach as yield. Check IR emission for `.await`.

### break (L6813) and continue (L6816)
These likely map to `br label` or similar. Check IR emission.

### labeled (L6810)
`.labeled label body` likely maps to IR `block` instruction. Check IR emission.

### HOW TO CHECK IR EMISSION:
```
lean_hover_info on LowerCodeCorr constructors
```
Or grep:
```
grep -n "yield\|await\|break\|continue\|labeled" VerifiedJS/Wasm/Lower.lean | head -30
```

### PROOF TEMPLATE (from return-none at L6764):
```lean
| .yield (some arg) delegate =>
  -- 1. Unfold the LowerCodeCorr hypothesis to get IR code
  obtain ⟨irCode, hirCorr, hirPrefix⟩ := hlower
  -- 2. Show irCode is the expected instruction(s)
  simp [Lower.lowerExpr] at hirCorr  -- or whatever the lowering function is
  -- 3. Show irStep? on the instruction produces a matching step
  refine ⟨ir₂, ?_, ?_⟩
  ...
```

Adapt this template for each 1:1 case.

## PRIORITY 1: callIndirect exfalso (L10838)

Check if `ANF.Expr.supported` or `Flat.Expr.supported` excludes `.callIndirect`. If so:
```lean
| .callIndirect typeIdx => exfalso; simp [supported] at h_supported
```

Look for the supported definition:
```
grep -n "def supported" VerifiedJS/ANF/Syntax.lean VerifiedJS/Flat/Syntax.lean
```

## PRIORITY 2: Compound step_sim cases (L6738-6759)

These 6 sorries (let, seq, if, while_, throw, tryCatch) are 1:N cases. They need multiple IR steps.

For each one, check if `step_sim_stutter` already handles it (like return-some). If not, add an explicit match.

Start with `throw` — it's likely simplest:
1. Check IR emission for `.throw`
2. If it emits `[pushArg, throw_]`, that's 2 instructions
3. Add a `| .throw arg =>` case in `step_sim_stutter` with a lemma showing 2 IR steps

## File: `VerifiedJS/Wasm/Semantics.lean`
## Log to agents/wasmspec/log.md

## IMPORTANT: Your runs are taking 1-2+ hours. Focus on ONE case at a time. Get yield or await closed first, then move on.
