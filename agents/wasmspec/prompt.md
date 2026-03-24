# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## TASK 0: Close EmitSimRel step_sim sorries (12 remain)

EmitSimRel.step_sim (line 6974) has 12 sorry sites. The pattern for each instruction case:

1. Extract `EmitCodeCorr` from `hrel.hcode` using `hcode_ir ▸ hrel.hcode`
2. Use `EmitCodeCorr.xxx_inv` to get Wasm code shape
3. Compute `irStep?` result using equation lemma
4. Compute `Wasm.step?` result using simp
5. Build post-step `EmitSimRel`

**Priority order** (easiest first):
- **L6986** (empty code `[]`): label-pop or frame-return. Unfold `irStep?` for `code = []`, dispatch on labels/frames.
- **L7481-7487** (binOp type mismatch): Close by showing IR traps → Wasm traps. Pattern:
  ```lean
  simp [irStep?, hcode_ir, withI32Bin] at hstep
  ```
- **L7582, L7650** (binOp general case): Same as above but for `v1 :: v2 :: stk` with wrong types.
- **L7849, L7852** (relOp): Same pattern as binOp.
- **L8050, L8053, L8056** (remaining): Check what instruction, apply same pattern.
- **L6878** (`emit_globals_init_valcorr`): Blocked on `irTypeToValType` private. **FIX FIRST**: make `irTypeToValType` public in Emit.lean (remove `private`), then `cases t <;> simp [irTypeToValType, irValueDefault_corr]`.

## TASK 1: Close LowerSimRel step_sim sorries (14 remain)

LowerSimRel.step_sim (line 6033) has 14 sorry sites (lines 6021, 6094, 6139-6178). These are harder — each needs:
1. Show how `lower` maps the ANF expression to IR code
2. Match ANF step to IR step sequence

**Easiest**: break/continue/labeled/return (lines 6163-6178) — these produce events, IR code should be short.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
