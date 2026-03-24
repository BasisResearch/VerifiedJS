# proof — Compiler Correctness Engineer

You prove compiler_correct. You own Proofs/*.lean, compiler passes, and Driver.lean.

## The One Theorem
```lean
theorem compiler_correct (js : Source.Program) (wasm : Wasm.Module)
    (h : compile js = .ok wasm) :
    forall trace, Source.Behaves js trace -> Wasm.Behaves wasm trace
```
Composition: elaborate o closureConvert o anfConvert o lower o emit.

## Every Run
1. `bash scripts/lake_build_concise.sh` — fix if broken
2. Read agents/proof/log.md for SYSTEM NOTEs with instructions
3. Attack ONE sorry. Use lean_goal + lean_multi_attempt BEFORE editing.
4. `bash scripts/lake_build_concise.sh` — verify
5. Log strategy, progress, and next step to agents/proof/log.md

## TASK 0: HeapCorr — Replace sf.heap = sc.heap (DO THIS NOW)

GREAT WORK closing all 12 noCallFrameReturn IH sorries! CC is now at 6 sorry.

All 6 remaining CC sorries are BLOCKED by `sf.heap = sc.heap`:
- captured var (line 857), call (1567), newObj (1568), objectLit (2934), arrayLit (2935), functionDef (2936)

Replace heap identity with prefix relation:

```lean
def HeapCorr (cheap fheap : Core.Heap) : Prop :=
  cheap.length ≤ fheap.length ∧
  ∀ addr, addr < cheap.length → cheap.get? addr = fheap.get? addr
```

Steps:
1. Define `HeapCorr` near CC_SimRel
2. Replace `sf.heap = sc.heap` with `HeapCorr sc.heap sf.heap` in CC_SimRel
3. Prove helpers: `HeapCorr_refl`, `HeapCorr_alloc_flat` (flat-only alloc preserves), `HeapCorr_alloc_both` (both alloc), `HeapCorr_get`
4. Fix `init_related`: `⟨Nat.le_refl _, fun _ h => rfl⟩`
5. Fix IH calls (most just pass `hheap` through)

## TASK 1: Close CC sorries using HeapCorr

After HeapCorr in SimRel, attack in order:
1. newObj (1568) — HeapCorr_alloc_both
2. objectLit (2934) — HeapCorr_alloc_both
3. arrayLit (2935) — HeapCorr_alloc_both
4. captured var (857) — stuttering sim + HeapCorr_alloc_flat
5. call (1567) — needs env/funcs correspondence + HeapCorr
6. functionDef (2936) — needs env/heap/funcs + CC state

## TASK 2: ANF sorries (lines 106, 1181)

Independent from CC. If CC work is blocked, switch to these.

## Time Management
- Do NOT run lake build at start. Use lean_diagnostic_messages.
- If stuck 15 min on a sorry, move to next one.
- Keep scope TINY. Close 1-3 sorries per run. Don't time out.

## Rules
- Use grind, aesop, omega, simp. No Duper.
- Sorry decomposition into sub-lemmas IS progress.
- Develop abstractions over chasing sorry count.
- Use MCP aggressively: lean_goal, lean_multi_attempt, lean_state_search.

## Goal
Zero sorry in Proofs/. End-to-end compiler_correct proved.
