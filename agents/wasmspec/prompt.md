# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 20 (in Semantics.lean)

### TASK 1: Close EmitSimRel call/callIndirect (L9098, L9101)

All constructors + inversion lemmas exist. Follow the `return_` pattern (L9342-9374):

```lean
      | .call funcIdx =>
          have hc : EmitCodeCorr (IRInstr.call funcIdx :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.call_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- Wasm code = .call funcIdx :: rest_w
            -- Case split on s1.funcs[funcIdx]? and s1.stack length
            -- Use irStep?_eq_call for IR step
            -- Use step?_eq_call (or derive from step? definition) for Wasm step
            -- Both push a new frame with the function's locals
            -- Stack correspondence: args consumed from stack, pushed to locals
            -- hframes_one: THIS MAY BREAK — call pushes a frame, so frames.length > 1
            -- If hframes_one = (s1.frames.length = 1), after call it becomes 2
            -- WORKAROUND: prove the function body executes and returns before
            --   the outer proof needs hframes_one again, OR generalize hframes_one
            sorry
          · exact hf.elim
```

**BLOCKER**: `hframes_one` asserts exactly 1 frame. A `call` pushes a second frame. You may need to:
1. Generalize `hframes_one` to `hframes_len` (frames.length = s1.frames.length) and handle nested frames
2. OR prove that call + body + return is a multi-step that restores frames to 1

If `call` is blocked by `hframes_one`, skip to TASK 2.

### TASK 2: Close EmitSimRel memoryGrow (L9448)

Simpler — no frame changes. Pattern:
```lean
      | .memoryGrow =>
          have hc : EmitCodeCorr (IRInstr.memoryGrow :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.memoryGrow_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- IR: pop i32 size from stack, grow memory, push old size (or -1)
            -- Wasm: .memoryGrow 0 does the same
            -- Use irStep?_eq_memoryGrow (if it exists, or derive from irStep? def)
            -- Match stack/memory state
            match hstk : s1.stack with
            | [] =>
              -- empty stack: both trap
              sorry -- derive from irStep? and step? definitions
            | v :: stk =>
              sorry -- case split on v type, then memory grow success/failure
          · exact hf.elim
```

Use `lean_goal` at L9448 to see the exact goal state, then `lean_multi_attempt` to test tactics.

### TASK 3: Close EmitSimRel br/brIf (L9338, L9341)

Both need label index correspondence (`hlabels` maps IR label names to Wasm label indices). Pattern:
```lean
      | .br label =>
          have hc : EmitCodeCorr (IRInstr.br label :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.br_inv with ⟨idx, rest_w, hcw, hrest⟩ | hf
          · -- hlabels maps label → idx
            -- IR: br label pops to label frame
            -- Wasm: br idx pops to idx-th label frame
            -- Need hlabel_content to show corresponding frames
            sorry
          · exact hf.elim
```

### LowerSimRel step_sim sorries (12 total, L6261-L6338)
```
L6261  let        sorry — multi-step (rhsCode + localSet + bodyCode)
L6269  seq        sorry — multi-step (aCode + drop + bCode)
L6273  if         sorry — multi-step (condCode + if_)
L6276  while      sorry — needs labels (block/loop)
L6279  throw      sorry — multi-step
L6282  tryCatch   sorry — opaque
L6323  return(some) sorry — 2 IR steps (argCode + return_)
L6326  yield      sorry — opaque
L6329  await      sorry — opaque
L6332  labeled    sorry — needs labels
L6335  break      sorry — needs labels
L6338  continue   sorry — needs labels
```

**ARCHITECTURAL BLOCKER**: `step_sim` is 1:1 (one ANF step → one IR step). Most cases need 1:N. The `step_sim_stutter` at L9454 already has the right signature. Focus on closing EmitSimRel cases first (TASK 1-3), then restructure LowerSimRel.

### Init sorries (3: L9607, L9622, L9646)
All need `LowerSimRel.init` with `LowerCodeCorr` for the initial program. `lowerExpr` is `partial`, so equation lemmas may not be available for `simp`. Try `unfold lowerExpr` or `delta lowerExpr`.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
- Do TASK 2 (memoryGrow) FIRST — it's the quickest win (no frame issues)
