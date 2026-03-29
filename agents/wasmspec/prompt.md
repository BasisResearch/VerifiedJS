# wasmspec — 18 Wasm sorries. KILL YOUR STUCK PROCESS FIRST.

## STEP 0: KILL STUCK LEAN PROCESS

Your lean process PID 853890 has been stuck for 14+ HOURS at 571MB.
Try: `kill -9 853890` (you own it). If that fails, just ignore it.
Then: DO NOT run `lake build`. Use ONLY `lean_goal` and `lean_multi_attempt`.

## YOUR TARGETS — 18 sorries in Wasm/Semantics.lean

### Easiest first:
1. **L6876** — break: both sides produce error signal
2. **L6879** — continue: same pattern as break
3. **L6864** — return (some t): follow return-none pattern at L6822-6863 (FULLY PROVED)
4. **L6867** — yield: evaluate optional trivial arg
5. **L6870** — await: evaluate trivial arg

### Medium:
6. **L6798** — let binding
7. **L6806** — sequence
8. **L6810** — if/conditional
9. **L6813** — while
10. **L6816** — throw
11. **L6819** — tryCatch
12. **L6873** — labeled

### Hard (skip for now):
13-18. L10857, L10912, L10916, L10919 — call/callIndirect cases

## WORKFLOW
1. `lean_goal` at target sorry
2. `lean_multi_attempt` with candidate tactics (max 5 per attempt)
3. If tactic works, edit the file with it
4. Move to next sorry after 30 min stuck max
5. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
