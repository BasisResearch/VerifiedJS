# jsspec — PIVOT TO WASM SORRIES. wasmspec is DEAD (16h zombie).

## STATUS: ANF sorries are ALL blocked by continuation mismatch. Excellent analysis. PIVOT.

Your ANF analysis was perfect — all 17 sorries need `normalizeExpr_labeled_step_sim` generalized to remove the faithful-k requirement. That's a deep refactor. NOT your job right now.

## NEW MISSION: Close Wasm sorries in Wasm/Semantics.lean

wasmspec has been ZOMBIE for 16+ hours. It will timeout at ~23:00. YOU take its Wasm sorries.

### Wasm Sorry Map (16 actual sorries, 18 grep-c):

#### EASIEST (start here — 5 sorries):
1. **L6876** — break: both sides produce error signal
2. **L6879** — continue: same pattern as break
3. **L6864** — return (some t): follow the return-none pattern at L6822-6863 (FULLY PROVED just above)
4. **L6867** — yield: evaluate optional trivial arg
5. **L6870** — await: evaluate trivial arg

#### MEDIUM (7 sorries):
6. **L6798** — let binding
7. **L6806** — sequence
8. **L6810** — if/conditional
9. **L6813** — while
10. **L6816** — throw
11. **L6819** — tryCatch
12. **L6873** — labeled

#### HARD (4 sorries — skip for now):
13-16. **L10857, L10912, L10916, L10919** — call/callIndirect

### APPROACH:
1. Read the proven cases above L6798 to understand the proof pattern (especially return-none at L6822-6863)
2. `lean_goal` at L6876 to see exact break goal
3. `lean_multi_attempt` with: `["simp [step]", "rfl", "exact absurd", "omega", "contradiction", "simp [Wasm.step?, Wasm.evalExpr]"]`
4. When a tactic works → Edit the file to replace sorry
5. Build: `lake build VerifiedJS.Wasm.Semantics`
6. Move to next sorry. Max 20 min per sorry.

### KEY INSIGHT:
- Break/continue should be near-identical (both produce error/abort signals)
- Return(some t) should follow return(none) which is already proven right above
- yield/await are similar to return

### CONSTRAINTS:
- CAN edit: `VerifiedJS/Wasm/Semantics.lean`
- DO NOT edit: `VerifiedJS/Proofs/*.lean`
- Stage helpers in `.lake/_tmp_fix/` if needed
- LOG every 30 min to agents/jsspec/log.md

### ANF STATUS (for reference):
Your analysis is saved in `.lake/_tmp_fix/anf_sorry_analysis.lean`. When wasmspec restarts at ~23:00, supervisor will redirect someone to ANF generalization. For now, Wasm is higher priority.
