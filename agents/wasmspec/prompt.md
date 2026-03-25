# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## TASK 0: Close EmitSimRel sorries (12 remain)

EmitSimRel.step_sim has 12 sorry sites. For each case:
1. Extract `EmitCodeCorr` from `hrel.hcode` using `hcode_ir ▸ hrel.hcode`
2. Use `EmitCodeCorr.xxx_inv` to get Wasm code shape
3. Compute `irStep?` result using equation lemma
4. Compute `Wasm.step?` result using simp
5. Build post-step `EmitSimRel`

**Actual sorry locations** (verify with `lean_goal`):

| Line | Case | Difficulty |
|------|------|-----------|
| 6880 | `emit_globals_init_valcorr` | Make `irTypeToValType` public in Emit.lean first |
| 6945 | `hmemory` init | Need `emit_preserves_memories` lemma |
| 6993 | empty code `[]` | Label-pop / frame-return |
| 7499 | `.load t offset` | Memory load simulation |
| 7502 | `.store t offset` | Memory store simulation |
| 7505 | `.store8 offset` | Memory store8 simulation |
| 7918 | `.call funcIdx` | Function call simulation |
| 7921 | `.callIndirect typeIdx` | Indirect call simulation |
| 8122 | `.br label` | Unconditional branch |
| 8125 | `.brIf label` | Conditional branch |
| 8128 | `.return_` | Return from function |
| 8198 | `.memoryGrow` | Grow memory |

**Easiest first**: L8122 (br), L8125 (brIf), L8128 (return_) — these are control flow, short IR/Wasm code. Follow the pattern from `.block` (L7922-7960) which is already proved.

**L6880**: Make `irTypeToValType` public in Wasm/Emit.lean (remove `private`), rebuild, then `cases t <;> simp [irTypeToValType]`.

## TASK 1: Close LowerSimRel sorries (14 + 3 init)

Lines 6021, 6094, 6139-6178 (14 step_sim cases) + L8357, L8372, L8396 (3 init).

**Easiest**: L6163-6178 (break/continue/labeled/return) — these produce events and have short IR code.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
