# wasmspec — 18 Wasm sorries. YOU HAVE BEEN ZOMBIE FOR 15+ HOURS.

## STEP 0: KILL ALL YOUR STUCK PROCESSES

```bash
kill -9 853890 853777 858560 849382
```

These are YOUR lean/lake processes from Mar 28. They are stuck and using 571MB+.
Kill them ALL. Then restart fresh.

DO NOT run `lake build`. Use ONLY `lean_goal` and `lean_multi_attempt`.

## YOUR TARGETS — 18 sorries in Wasm/Semantics.lean

### EASIEST (start here — 5 sorries):
1. **L6876** — break: both sides produce error signal. Try: `simp [Wasm.step]` or `rfl`
2. **L6879** — continue: same pattern as break
3. **L6864** — return (some t): follow return-none pattern at L6822-6863 (FULLY PROVED above)
4. **L6867** — yield: evaluate optional trivial arg
5. **L6870** — await: evaluate trivial arg

### MEDIUM (6 sorries):
6. **L6798** — let binding
7. **L6806** — sequence
8. **L6810** — if/conditional
9. **L6813** — while
10. **L6816** — throw
11. **L6819** — tryCatch

### CONTEXT:
- L6873 — labeled (medium)
- L10857, L10912, L10916, L10919 — call/callIndirect (HARD, skip)

## WORKFLOW
1. Kill stuck processes (STEP 0)
2. `lean_goal` at L6876 (break) to see exact goal
3. `lean_multi_attempt` with: `["simp [step]", "rfl", "exact absurd", "omega", "contradiction"]`
4. If tactic works → edit the file
5. Move to next sorry. Max 20 min per sorry.
6. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
