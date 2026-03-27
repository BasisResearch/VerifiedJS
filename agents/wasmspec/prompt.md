# wasmspec — GREAT PROGRESS: Wasm 28→24 (-4). Keep pushing.

## CURRENT STATUS
You've closed 4 Wasm sorries this session. Excellent work.

## REMAINING PRIORITIES (24 sorries total)

### P0: store (L9295) + store8 (L9754)
If not already done, uncomment these proofs. They exist in comments.

### P1: binOp trap cases (~L10005, L10083, L10090)
These are mechanical. Pattern:
- Stack underflow: `have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen`
- Type mismatch: use `step?_eq_trap` + construct the EmitSimRel record

Use `lean_goal` + `lean_multi_attempt` on each.

### P2: if_ proof (L10443 area)
If the if_ uncomment still has errors:
- Use `by_cases h0 : cond = 0` instead of `match hcond : decide (cond = 0)`
- For true branch (cond ≠ 0): use `irStep?_eq_if_true`
- For false branch (cond = 0): use `irStep?_eq_if_false`

### SKIP (architecturally blocked):
- Inner step_sim (L6470-6548) — 1:N mapping, needs architecture change
- call (L10350/L10354) — multi-frame, needs hframes_one relaxation
- callIndirect (L10357) — skip
- memoryGrow (L11082) — skip
- br/brIf (L10665/L10748) — complex label unwinding

### STRETCH: br (L10665) and brIf (L10748)
If P0-P2 are done, attempt br/brIf. These need label unwinding:
- `br label`: pop `label` frames from labels stack, jump to onBranch code
- `brIf label`: check condition, then either br or continue
- Key: show EmitCodeCorr is preserved through label pops

## DO NOT touch:
- Any file other than Wasm/Semantics.lean
- The inner step_sim cases (L6470-6548)

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
