# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 20 (in Semantics.lean)

### TASK 1 (DO FIRST): Close init sorries (L9813, L9828, L9852)

All 3 are the same: `LowerSimRel.init prog irmod hlower (by sorry)`.

The `by sorry` must prove: `LowerCodeCorr prog.main (irInitialState irmod).code`.

`lowerExprWithExn` is NOW PUBLIC (no longer blocked!). The proof:
1. Unfold `Wasm.lower` from `hlower` to get the generated IR code
2. Show `irInitialState irmod` has `.code = [call startIdx]` or `[]`
3. Show the lowered ANF expression satisfies `LowerCodeCorr`

Strategy:
```lean
-- At each `by sorry`:
-- hlower : Wasm.lower prog = .ok irmod
-- Need: LowerCodeCorr prog.main (irInitialState irmod).code
--
-- Wasm.lower calls lowerExprWithExn on prog.main.
-- irInitialState sets code from the lowered result.
-- So (irInitialState irmod).code IS the lowered code.
-- LowerCodeCorr should hold by construction (lower produces LowerCodeCorr-conforming code).
--
-- Use lean_goal at each sorry to see the exact goal, then:
-- unfold Wasm.lower at hlower (or simp [Wasm.lower] at hlower)
-- extract the code from hlower
-- construct LowerCodeCorr by matching the ANF expression to the IR code
```

Use `lean_goal` at L9813 column 38 to see the exact proof state.

### TASK 2: Close L9628 (memoryGrow no-memory case)

This sorry is in the branch where `hmemory` gives `w.store.memories[0]? = none ∧ ir.memory.size = 0`. But then we're in the `| .i32 pages :: stk =>` case, meaning the IR has memory (just size 0). Show:
- IR memoryGrow with 0-size memory and pages on stack → either grows (allocating pages*65536 bytes) or fails
- Wasm has no memory (`memories[0]? = none`) → step? for memoryGrow returns trap or -1
- Both produce matching events

Use `lean_goal` at L9628 to see the proof state, then match IR and Wasm behaviors.

### TASK 3: Close br/brIf if possible (L9394, L9397)

The `br_inv` gives `wcode = Instr.br idx :: rest_w`. Need to connect:
- IR: `irFindLabel? s1.labels label = some (pos, lbl)` → branch to `lbl.onBranch`
- Wasm: `br idx` → branch to label at index `idx` in Wasm label stack

Missing link: how does IR label name `label` relate to Wasm label index `idx`? The `br_` EmitCodeCorr constructor has both `label` and `idx` but doesn't constrain their relationship. You may need to add an invariant to EmitSimRel connecting IR label names to Wasm label indices.

If this is too hard, skip and focus on TASK 1+2.

### LowerSimRel sorries (12: L6261-L6338)

ALL blocked by 1:N stepping. Don't work on these unless you restructure step_sim to multi-step.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
- Do TASK 1 FIRST — init sorries are the quickest wins
