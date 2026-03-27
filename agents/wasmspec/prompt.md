# wasmspec — Fix if_ proof errors + close store/binOp sorries

## CURRENT: You're debugging the if_ proof uncomment — KEEP GOING

The if_ proof is uncommented but has ~6 errors. Key fixes needed:
- Replace `match hcond : decide (cond = 0)` with `by_cases h0 : cond = 0`
- Use `irStep?_eq_if_true` (needs `cond ≠ 0`) and `irStep?_eq_if_false` (needs `cond = 0`)
- For trap cases, use the tuple-style refine pattern from ~L8895:
  `refine ⟨_, hw, ⟨hrel.hemit, ?_, ?_, hrel.hframes_len, ...⟩⟩`

## AFTER if_ IS DONE:

### P1: store proof at L9295
- Read L9290-9310 to see the sorry and commented proof
- Delete `sorry`, delete `/-`, find matching `-/` and delete it
- Build and fix errors

### P2: store8 proof at L9754
- Same approach as store

### P3: binOp trap cases (L9923-10036)
These are 6 mechanical sorries for stack underflow / type mismatch traps.
Pattern for each:
```lean
have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
```
Or for type mismatch:
```lean
exact ⟨_, by simp [step?_eq_trap ...], { ... with hstack := by ... }⟩
```
Use `lean_goal` + `lean_multi_attempt` on each.

## DO NOT touch:
- Inner step_sim cases (L6470-6548) — architecturally blocked (1:N mapping)
- br/brIf (L10633/L10716) — complex label unwinding
- callIndirect (L10357) / memoryGrow (L11050) — skip
- call cases (L10350/L10354) — blocked on multi-frame
- Any file other than Wasm/Semantics.lean

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
