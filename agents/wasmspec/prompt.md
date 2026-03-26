# wasmspec — Close memoryGrow no-memory (L9972)

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 21 (in Semantics.lean)

### TASK 1 (DO FIRST): Close memoryGrow no-memory sorry at L9972

This is a **1-line fix**. The sorry is in the `none` branch of `rcases hrel.hmemory`:

```lean
rcases hrel.hmemory with hmem_eq | ⟨hmem_none, hmem_sz⟩
```

In the second branch, `hmem_none : w.store.memories[0]? = none`.
But `hrel.hmemory_nonempty : 0 < w.store.memories.size`.

These CONTRADICT — if size > 0 then `[0]?` is `some _`, not `none`.

**Replace the `sorry` at L9972 with:**
```lean
                exfalso
                have h := hrel.hmemory_nonempty
                simp [Array.getElem?_eq_none_iff] at hmem_none
                omega
```

If `Array.getElem?_eq_none_iff` doesn't exist, try:
```lean
                exfalso
                have : (s2.store.memories[0]? ≠ none) := by
                  exact Option.isSome_iff_ne_none.mp (Array.getElem?_isSome.mpr hrel.hmemory_nonempty)
                exact this hmem_none
```

Or more simply:
```lean
                exact absurd hmem_none (by simp [show 0 < s2.store.memories.size from hrel.hmemory_nonempty])
```

Use `lean_multi_attempt` at L9972 to test which tactic works BEFORE editing.

### TASK 2: Investigate br/brIf architecture

The br sorry at L9715 needs a connection between:
- `irFindLabel? ir.labels label` → returns `(ir_idx, irLbl)` (by name lookup)
- `resolveBranch? w.labels idx` → resolves by numeric index (from `Instr.br idx`)

**Problem**: EmitCodeCorr `br_` stores `idx` (from emit-time `resolveLabelIdx`), but there's NO proof that `ir_idx = idx`. They're produced by different name lookups on different data structures.

**Solution needed**: Add to EmitSimRel:
```lean
hlabel_name_resolve : ∀ (label : String) (ir_idx : Nat) (irLbl : IRLabel),
  irFindLabel? ir.labels label = some (ir_idx, irLbl) →
  ∃ wLbl wLabels', resolveBranch? w.labels ir_idx = some (wLbl, wLabels') ∧
    EmitCodeCorr irLbl.onBranch wLbl.onBranch ∧
    EmitCodeCorr irLbl.onExit wLbl.onExit ∧
    irLbl.isLoop = wLbl.isLoop
```

This follows from `hlabels` + `hlabel_content` + a lemma about `irFindLabel?` returning valid indices. BUT you also need `ir_idx = idx` from the Wasm code — which requires tracking that emit-time and runtime label stacks have the same name ordering.

**If TASK 2 seems too complex, SKIP IT.** Focus on closing L9972.

### DON'T work on:
- LowerSimRel (12 sorries) — blocked by 1:N stepping
- call/callIndirect — blocked by multi-frame (`hframes_one`)
- init sorries — need LowerCodeCorr from lower proof

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
- Do TASK 1 FIRST — it's a 1-sorry win in 5 minutes
