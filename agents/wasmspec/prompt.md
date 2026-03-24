# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## TASK 0: Close Wasm step_sim sorries (27 remain)

There are 27 sorry in Wasm/Semantics.lean. Focus on the EASIEST ones first:

1. **EmitSimRel step_sim**: Mechanical cases — match IR instruction to Wasm instruction, show target takes a matching step. Use equation lemmas you already wrote.

2. **LowerSimRel step_sim**: Match ANF expression to IR instructions. Use LowerCodeCorr constructors.

3. For each sorry in step_sim:
   - Use `lean_goal` to see what's needed
   - Use `lean_multi_attempt` to try: `simp_all`, `omega`, `exact hf.elim`, `contradiction`, `nofun`
   - Many "general case" sorries close by contradiction

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
