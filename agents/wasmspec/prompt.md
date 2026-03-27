# wasmspec — Uncomment if_ proof + close store/binOp sorries

## STEP 0: Build check
```
lake build VerifiedJS.Wasm.Semantics 2>&1 | grep 'error:'
```
If broken, fix or revert to sorry FIRST.

## block and loop are DONE ✓ (uncommented and proven)

## PRIORITY 0: UNCOMMENT if_ proof at L10443 — FREE sorry

Line 10443: `| .if_ result then_ else_ => sorry`
Line 10444: `/-` — start of commented-out proof
The proof is ALREADY WRITTEN in the comment block starting at L10444.

Steps:
1. Delete the `sorry` on L10443
2. Delete the `/-` on L10444
3. Find the matching `-/` and delete it
4. Build to verify: `lake build VerifiedJS.Wasm.Semantics`
5. If build fails, use `lean_diagnostic_messages` to fix

## PRIORITY 1: UNCOMMENT store proof at L9295 — FREE sorry

Line 9295: `sorry`
Line 9296: `/-` — start of commented-out proof

Steps:
1. Delete `sorry` on L9295
2. Delete `/-` on L9296
3. Find the matching `-/` and delete it
4. Build to verify

## PRIORITY 2: UNCOMMENT store8 proof at L9754 — FREE sorry

Line 9754: `sorry`
The commented-out proof should be immediately after.
Same approach as store.

## PRIORITY 3: binOp trap cases — 6 sorries around L9923-10036

These are stack underflow / type mismatch trap cases. Each needs:
```lean
have hlen := hrel.hstack.1; rw [hstk] at hlen; simp at hlen
```
Or for trap record construction:
```lean
exact ⟨_, by simp [step?_eq_trap ...], { ... with hstack := by ... }⟩
```
Use `lean_goal` + `lean_multi_attempt` on each.

## DO NOT touch:
- Inner step_sim cases (L6470-6548) — architecturally blocked (1:N mapping)
- br/brIf (L10648/L10731) — complex label unwinding
- callIndirect (L10357) / memoryGrow (L11065) — skip
- call cases (L10350/L10354) — blocked on multi-frame

## Build: `lake build VerifiedJS.Wasm.Semantics`
## Log progress to agents/wasmspec/log.md.
