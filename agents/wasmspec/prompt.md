# wasmspec — Close EmitSimRel call + callIndirect

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 20 (in Semantics.lean)

### TASK 1 (DO FIRST): Close EmitSimRel `.call funcIdx` (L9148)

The sorry is in `EmitSimRel.step_sim`, case `| .call funcIdx =>`.

**What you have:**
- `EmitCodeCorr.call_inv`: gives `wcode = Instr.call funcIdx :: rest_w ∧ EmitCodeCorr rest rest_w`
- `irStep?_eq_call` (L4986): exact IR call stepping equation
- `step?_eq_call_valid` (L2879): exact Wasm call stepping equation
- `step?_eq_call_oob` (L2897): Wasm call with OOB function index
- `step?_eq_call_underflow` (L2907): Wasm call with stack underflow

**Pattern** (same as block/end/load/store cases):
```lean
| .call funcIdx =>
    have hc : EmitCodeCorr (IRInstr.call funcIdx :: rest) s2.code := hcode_ir ▸ hrel.hcode
    rcases hc.call_inv with ⟨rest_w, hcw, hrest⟩ | hf
    · -- Specific case: Wasm code = call funcIdx :: rest_w
      -- Case 1: funcIdx valid in both IR and Wasm
      -- Both do call: push frame, enter function body
      -- Use hrel.hfuncs (function correspondence) to connect
      -- Case 2: funcIdx OOB → both trap
      -- Case 3: stack underflow → both trap (stack_corr preserves length)
      sorry
    · exact hf.elim
```

**Key:** Both IR and Wasm call the same funcIdx. The EmitCodeCorr `call_` constructor preserves funcIdx. You need:
1. `hrel.hfuncs` or similar to show IR and Wasm have the same function at funcIdx
2. `hrel.hstack` to show stack correspondence (args match)
3. After the call, the new frame's code corresponds (function body was emitted)

Use `lean_goal` at L9148 to see the exact proof state. Use `lean_multi_attempt` to test tactics.

### TASK 2: Close EmitSimRel `.callIndirect typeIdx` (L9151)

Same pattern as call but with `callIndirect_inv`. The `callIndirect_` constructor maps `IRInstr.callIndirect typeIdx` to `Instr.callIndirect typeIdx 0`.

### TASK 3 (if time): Init sorries (L9813, L9828, L9852)

All need `LowerCodeCorr prog.main (irInitialState irmod).code`.

Since `lower` sets `startFunc := none` (proved by `lower_startFunc_none`), `(irInitialState irmod).code = []`.

So the goal is `LowerCodeCorr prog.main []`. Check if there's a `LowerCodeCorr` constructor for empty code. If not, this needs a new constructor or architectural change. Skip if blocked.

### LowerSimRel sorries (12: L6261-L6338)

ALL blocked by 1:N stepping. Don't work on these.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
- Do TASK 1 FIRST — call is the most impactful win
