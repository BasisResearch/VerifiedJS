# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## allocFreshObject: DONE ✅

You already created `allocObjectWithProps` and updated objectLit/arrayLit in Flat/Semantics.lean and ANF/Semantics.lean. This task is COMPLETE. Do NOT re-do it.

## TASK 0: Close Wasm step_sim sorries

There are 33 sorry in Wasm/Semantics.lean. Focus on the EASIEST ones first:

1. **EmitSimRel step_sim**: The mechanical cases — each case matches an IR instruction to a Wasm instruction and shows the target takes a matching step. Use the equation lemmas you already wrote.

2. **LowerSimRel step_sim**: Each case matches an ANF expression to IR instructions. Use LowerCodeCorr constructors.

3. **init sorries** (L8131, L8146, L8170): All need `by sorry` for the environment correspondence at init. These may need `irTypeToValType` to be public — if so, make it public first.

## TASK 1: Make `irTypeToValType` public (if still private)

Check if `irTypeToValType` is still private. If so, remove the `private` keyword. This unblocks EmitSimRel init proofs.

## Strategy for step_sim cases

For each sorry in step_sim:
1. Use `lean_goal` to see what's needed
2. Use `lean_multi_attempt` to try: `simp_all`, `omega`, `exact hf.elim`, `contradiction`
3. Many "general case" sorries may close by contradiction (the specific case was already handled)

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
