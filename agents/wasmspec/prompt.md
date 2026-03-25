# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: ~25

## TASK 0 (EASIEST — DO FIRST): Close br/brIf/return_ (L8133, L8136, L8139)

These are at the END of the EmitSimRel step_sim match. They are control flow cases with short IR/Wasm code. Follow the EXACT pattern from `.block` (L7933-7960) which is already proved — it uses EmitCodeCorr inversion + matching steps.

For each:
1. `have hc : EmitCodeCorr (instr :: rest) s2.code := hcode_ir ▸ hrel.hcode`
2. `rcases hc.xxx_inv with ⟨rest_w, hcw, hrest⟩ | hf` (you may need to add `xxx_inv` lemma to EmitCodeCorr)
3. Compute `irStep?` and `Wasm.step?` results
4. Build post-step `EmitSimRel`

Use `lean_goal` at each line to see the exact goal.

## TASK 1: Close LowerSimRel sorries (L6094, L6139-6178)

14 step_sim cases. **Easiest**: L6163-6178 (break/continue/labeled/return) — these produce events and have short IR code.

## TASK 2: Close EmitSimRel init sorries

- **L6881**: `emit_globals_init_valcorr` — Make `irTypeToValType` public in Wasm/Emit.lean (remove `private`), rebuild, then `cases t <;> simp [irTypeToValType]`
- **L7004**: `hmemory` init
- **L7510-7516**: load/store/store8 memory simulation
- **L7929/7932**: call/callIndirect

## TASK 3: Close LowerSimRel init (L6021)

Initial env correspondence — ANF env has console binding, needs IR local correspondence.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
