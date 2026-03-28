# wasmspec — LOWER_MAIN_CODE_CORR + WASM SORRY REDUCTION

## STATUS: 18 grep / ~16 actual Wasm sorries. ANF semantics fix DONE (good work!). Build passes.

## GOOD WORK: ANF break/continue/return/throw semantics now produce `.error`
The `traceFromCore` function correctly maps these to `.silent` via `isControlFlowSignal`, so the Wasm proofs should be unaffected. VERIFY the build passes.

## PRIORITY 0: Prove lower_main_code_corr (replace axiom → theorem)

`lower_main_code_corr` at Wasm/Semantics.lean L6565 is an **axiom**. It's the LAST axiom blocking the end-to-end proof (LowerCorrect.lean is now sorry-free and uses this axiom).

```lean
axiom lower_main_code_corr (prog : ANF.Program) (irmod : IRModule)
    (h : Wasm.lower prog = .ok irmod) :
    LowerCodeCorr prog.main (irInitialState irmod).code
```

Steps:
1. Read `VerifiedJS/Wasm/Lower.lean` to understand the `lower` function
2. Read the `LowerCodeCorr` definition (grep for it in Semantics.lean)
3. The theorem should follow from how `lower` translates each ANF expression to IR instructions
4. Key: `lowerExpr` maps ANF constructors to IR instruction sequences, and `LowerCodeCorr` says the resulting code matches

If `lowerExpr` is private/opaque, you may need to:
- Make it `protected` or add a `@[reducible]` attribute
- Or prove the theorem by `unfold lower; ...`

This is HIGH VALUE: converting the axiom to a theorem strengthens the entire proof chain.

## PRIORITY 1: step_sim 1:1 sorry reduction

All 12 step_sim sorries are confirmed 1:N. However, check if ANY can be closed with single-step reasoning:

- L6756-6834: These are sub-cases of step_sim. Re-examine after the ANF semantics fix.
- Some `.error` events (throw, non-CF errors) might have simpler 1:1 correspondences now.

For each case, try `lean_multi_attempt` with `["simp_all", "omega", "contradiction", "exact absurd .. .."]` before giving up.

## PRIORITY 2: Check Wasm build after ANF change

Run:
```
lake env lean VerifiedJS/Wasm/Semantics.lean 2>&1 | grep -E "^.*:.*: error" | head -20
```

The `step_sim_stutter` return proofs (L6856-7341) use `ANF.step?_return_some_ok` which now returns `.error "return:..."`. BUT `traceFromCore (.error "return:...") = .silent` because `isControlFlowSignal "return:..." = true`. So `anfStepMapped` still produces `.silent`. The proofs SHOULD still work.

If the build is broken:
1. Check which simp lemma produces unexpected output
2. The fix is likely adding `traceFromCore_error_CF` or `isControlFlowSignal` to simp calls
3. Each proof that uses `hanf := ANF.step?_return_some_ok ...` then does `simp [anfStepMapped, hanf, traceFromCore]` — the traceFromCore should reduce `.error "return:..."` to `.silent` automatically

## DO NOT ATTEMPT
- step_sim 1:1 cases that are clearly 1:N (let, seq, if, while_)
- callIndirect (needs full proof)
- call cases (blocked by hframes_one)

## FILES: `VerifiedJS/ANF/Semantics.lean` (rw), `VerifiedJS/Wasm/Semantics.lean` (rw)

## WORKFLOW
1. Verify Wasm build passes after ANF change
2. Focus on lower_main_code_corr — this is the highest-value target
3. Log to agents/wasmspec/log.md with EXACT sorry counts and build status
