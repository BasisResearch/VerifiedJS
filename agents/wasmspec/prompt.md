# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 20 (in Semantics.lean)

### TASK 1 (DO FIRST): Close EmitSimRel memoryGrow (L9510)

No frame changes, no labels — just stack + memory. Follow the exact pattern from `drop` (L9440-9506).

You need a Wasm `step?` equation lemma first. Write it near L5374:

```lean
/-- Wasm step? for memory.grow with i32 on stack (success). -/
theorem step?_eq_memoryGrow_ok (s : ExecState) (rest : List Instr)
    (delta : UInt32) (stk : List WasmValue)
    (hcode : s.code = Instr.memoryGrow 0 :: rest)
    (hstack : s.stack = .i32 delta :: stk)
    (hMem : 0 < s.store.memories.size)
    (hMaxOk : -- max check passes
      (if hLim : 0 < s.store.memLimits.size then
        match s.store.memLimits[0].max with
        | some maxPages => (s.store.memories[0]'hMem).size / 65536 + delta.toNat ≤ maxPages
        | none => (s.store.memories[0]'hMem).size / 65536 + delta.toNat ≤ 65536
      else (s.store.memories[0]'hMem).size / 65536 + delta.toNat ≤ 65536) = true) :
    let mem := (s.store.memories[0]'hMem)
    let oldPages := mem.size / 65536
    let grown := ByteArray.mk (mem.toList.toArray ++ Array.replicate (delta.toNat * 65536) 0)
    step? s = some (.silent, pushTrace { s with
      store := { s.store with memories := s.store.memories.set! 0 grown }
      code := rest
      stack := .i32 (UInt32.ofNat oldPages) :: stk } .silent) := by
  simp [step?, hcode, hstack, pop1?, hMem, pushTrace]
  sorry -- fill in the maxOk logic; may need split on memLimits
```

Then write the step_sim case at L9510:

```lean
      | .memoryGrow =>
          have hc : EmitCodeCorr (IRInstr.memoryGrow :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.memoryGrow_inv with ⟨rest_w, hcw, hrest⟩ | hf
          · -- Case split on IR stack
            match hstk : s1.stack with
            | [] =>
              -- Empty stack: IR traps
              have hir := irStep?_eq_trap_empty s1 rest hcode_ir hstk  -- or derive from irStep? def
              sorry -- both trap, match trace
            | .i32 pages :: stk =>
              -- i32 on stack: memory grow
              -- Case split on size check
              if hsize : s1.memory.size + pages.toNat * 65536 ≤ 65536 * 65536 then
                -- Success case
                have hir := irStep?_eq_memoryGrow_ok s1 rest pages stk hcode_ir hstk hsize
                rw [hir] at hstep
                simp only [Option.some.injEq, Prod.mk.injEq] at hstep
                obtain ⟨rfl, rfl⟩ := hstep
                -- Wasm side: use hmemory to get memories[0] = ir.memory
                -- Use hmemLimits to show max = none → newPages ≤ 65536 always true
                -- Build new EmitSimRel with updated memory + stack
                sorry -- fill in Wasm step + SimRel construction
              else
                -- Failure case: push 0xFFFFFFFF
                sorry -- both push -1, memory unchanged
            | v :: stk =>
              -- Non-i32 on stack: IR traps with type mismatch
              sorry -- both trap, match trace
          · exact hf.elim
```

Key hints:
- `hmemory` gives you `w.store.memories[0]? = some ir.memory` — use `Option.some.injEq` to get equality
- `hmemLimits` gives you `lim.max = none` — so the maxOk condition reduces to `newPages ≤ 65536`
- `hmemory_aligned` gives you `65536 ∣ ir.memory.size` — needed for oldPages computation
- Stack correspondence: old stack corresponded, push `IRValue.i32 oldPages` / `WasmValue.i32 oldPages` — use `IRValueToWasmValue.i32`

### TASK 2: Close EmitSimRel br/brIf (L9394, L9397)

Both need label index correspondence. Pattern:
```lean
      | .br label =>
          have hc : EmitCodeCorr (IRInstr.br label :: rest) s2.code := hcode_ir ▸ hrel.hcode
          rcases hc.br_inv with ⟨idx, rest_w, hcw, hrest⟩ | hf
          · sorry -- use hlabel_content to relate IR label → Wasm label idx
          · exact hf.elim
```

### TASK 3: Close EmitSimRel call/callIndirect (L9148, L9151)

**BLOCKER**: `hframes_one` asserts exactly 1 frame. A `call` pushes a second frame. Skip if blocked.

### LowerSimRel sorries (12 total, L6261-L6338)

**ARCHITECTURAL BLOCKER**: `step_sim` is 1:1 but most cases need 1:N. Focus on EmitSimRel first.

### Init sorries (3: L9669, L9684, L9708)

All need `LowerSimRel.init` with `LowerCodeCorr` for the initial program.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
- Do TASK 1 (memoryGrow) FIRST — it's the quickest win (no frame issues)
