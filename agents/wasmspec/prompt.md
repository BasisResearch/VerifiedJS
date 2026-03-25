# wasmspec — Close EmitSimRel br + brIf

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 21 (in Semantics.lean)

### TASK 1 (DO FIRST): Close EmitSimRel `.br label` (L9715)

The sorry is in `EmitSimRel.step_sim`, case `| .br label =>`.

**What you need to know:**
- IR `.br label` finds a label by name in `s1.labels` using `irFindLabel?`
- Wasm `.br idx` pops labels by numeric index
- EmitCodeCorr has a `br_` constructor: `IRInstr.br label` ↔ `Instr.br idx`
- The `hrel.hlabels` field gives `s1.labels.length = s2.labels.length`
- The `hrel.hlabel_content` gives correspondence at each label index

**Pattern:**
```lean
| .br label =>
    have hc : EmitCodeCorr (IRInstr.br label :: rest) s2.code := hcode_ir ▸ hrel.hcode
    rcases hc.br_inv with ⟨idx, rest_w, hcw, hrest⟩ | hf
    · -- Wasm code = Instr.br idx :: rest_w
      -- IR: irFindLabel? finds label at some index → jump
      -- Wasm: br idx pops idx labels
      -- Need: irFindLabel? label s1.labels = some (idx, onExit)
      --   AND hlabel_content shows onExit corresponds to Wasm label's onExit
      -- Use lean_goal at L9715 to see exact state
      sorry
    · exact hf.elim
```

**Key question:** How does `br_` connect `label` (a String) to `idx` (a Nat)? Use `lean_hover_info` on `br_` in EmitCodeCorr to see its constructor signature, then use `lean_goal` at L9715.

### TASK 2: Close EmitSimRel `.brIf label` (L9718)

Same pattern as br but conditional. IR pops a value, checks truthiness, then either branches or falls through. Wasm does `br_if idx` which pops i32.

### TASK 3: Close memoryGrow no-memory sorry (L9972)

This is the unreachable case where memory doesn't exist. Options:
1. Add `hmemory_exists : 0 < s2.store.memories.size` field to EmitSimRel (if you can prove it at init from `hemit`)
2. Or show it's implied by existing invariants

### DON'T work on:
- LowerSimRel (12 sorries) — blocked by 1:N stepping
- call/callIndirect — blocked by multi-frame (`hframes_one`)
- init sorries — architecturally blocked

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
- Do TASK 1 FIRST — br is the most tractable win
