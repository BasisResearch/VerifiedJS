# wasmspec — Close Wasm sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 22 (in Semantics.lean)

### TASK 1: Add EmitCodeCorr.load_i64 + store_i64 (closes 2 sorry)

L7974 and L8232 are blocked only by missing constructors. Add these to `EmitCodeCorr`:

```lean
  /-- i64.load maps to i64.load. REF: Emit.lean line 92. -/
  | load_i64 (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.load .i64 offset :: rest_ir)
        (.i64Load { offset := offset, align := 3 } :: rest_w)
  /-- i64.store maps to i64.store. REF: Emit.lean line 96. -/
  | store_i64 (offset : Nat) (rest_ir : List IRInstr) (rest_w : List Instr) :
      EmitCodeCorr rest_ir rest_w →
      EmitCodeCorr (.store .i64 offset :: rest_ir)
        (.i64Store { offset := offset, align := 3 } :: rest_w)
```

Then add inversion lemmas (mirror `load_i32_inv`/`store_i32_inv`):

```lean
theorem EmitCodeCorr.load_i64_inv {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.load .i64 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.i64Load { offset := offset, align := 3 } :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    False := by
  cases h with
  | load_i64 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim

theorem EmitCodeCorr.store_i64_inv {offset : Nat} {rest : List IRInstr} {wcode : List Instr}
    (h : EmitCodeCorr (IRInstr.store .i64 offset :: rest) wcode) :
    (∃ rest_w, wcode = Instr.i64Store { offset := offset, align := 3 } :: rest_w ∧ EmitCodeCorr rest rest_w) ∨
    False := by
  cases h with
  | store_i64 _ _ rw hrw => left; exact ⟨rw, rfl, hrw⟩
  | general _ _ _ _ hf _ => exact hf.elim
```

Update `EmitCodeCorr.head_inv` to include the new cases:
```lean
  | load_i64 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
  | store_i64 _ _ rw hrw => exact ⟨[_], rw, rfl, hrw⟩
```

Then prove L7974 and L8232 following the i32 pattern exactly:
- L7974: `rcases hc_full.load_i64_inv with ⟨rest_w, hcw, hrest⟩ | hf` then mirror L7758-7972
- L8232: `rcases hc_full.store_i64_inv with ⟨rest_w, hcw, hrest⟩ | hf` then mirror L7984-8230

You'll also need `irStep?_eq_load_i64` and `irStep?_eq_store_i64` (mirror the i32 versions at L5251 and L5279), and Wasm step lemmas `step?_eq_i64Load` / `step?_eq_i64Store`.

### TASK 2: Restructure LowerSimRel step_sim to multi-step

**ARCHITECTURAL BLOCKER**: `step_sim` (L6126) uses `∃ s2', irStep? s2 = some (t, s2')` (1 ANF step → 1 IR step). This is FALSE for return(some), throw, let, seq, if, while — all need multiple IR steps.

Change the conclusion to use `IRSteps`:

```lean
theorem step_sim (prog : ANF.Program) (irmod : IRModule) :
    ∀ (s1 : ANF.State) (s2 : IRExecState) (t : Core.TraceEvent) (s1' : ANF.State),
    LowerSimRel prog irmod s1 s2 → ANF.step? s1 = some (t, s1') →
    ∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
      IRSteps s2 ir_trace s2' ∧
      LowerSimRel prog irmod s1' s2' ∧
      observableEvents ir_trace = observableEvents [traceFromCore t] := by
```

Fix existing proofs (var case, return none) by wrapping single steps:
```lean
-- Where you had: exact ⟨_, hir, hrel'⟩
-- Change to:
exact ⟨_, [traceFromCore ct], .tail (.mk hir) (.refl _), hrel', rfl⟩
```

Then `step_sim_stutter` becomes trivial (or delete it, it's now identical to `step_sim`).

### TASK 3: After TASK 2, close return(some) at L6294

Add inner code correspondence to `return_some`:
```lean
  | return_some (arg : ANF.Trivial) (argCode : List IRInstr) :
      LowerCodeCorr (.trivial arg) argCode →  -- ADD THIS
      LowerCodeCorr (.«return» (some arg)) (argCode ++ [.return_])
```

Then prove the return(some) case using 2 IR steps (compose with IRSteps). Case split on `evalTrivial env t`:
- `.ok v`: ANF silent, IR executes argCode (1 step) then return_ (1 step)
- `.error msg`: ANF error, IR traps

### Emit sorries summary (7 remaining after TASK 1)
```
L8796  call           sorry — needs EmitCodeCorr.call constructor
L8799  callIndirect   sorry — needs EmitCodeCorr.callIndirect
L9036  br             sorry — needs label correspondence
L9039  brIf           sorry — needs label correspondence
L9146  memoryGrow     sorry — needs EmitCodeCorr.memoryGrow
L9305  init           by sorry — needs lowerExpr public
L9320  init           by sorry
L9344  init           by sorry
```

### Lower step_sim sorries (12, after restructure)
```
L6232  let            sorry — multi-step, no labels
L6240  seq            sorry — multi-step, no labels
L6244  if             sorry — multi-step, no labels
L6247  while          sorry — needs labels (block/loop)
L6250  throw          sorry — multi-step (throw_ret) or labels (throw_br)
L6253  tryCatch       sorry — opaque
L6294  return some    sorry — TASK 3 (2 IR steps)
L6297  yield          sorry — opaque
L6300  await          sorry — opaque
L6303  labeled        sorry — needs labels
L6306  break          sorry — needs labels
L6309  continue       sorry — needs labels
```

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
- Do TASK 1 FIRST — it's the quickest win (2 sorries, pattern already exists)
