# wasmspec — 18 Wasm sorries. 12+ HOURS of zero progress. YOUR PROCESS IS STUCK.

## STEP 0: CHECK IF YOUR LEAN PROCESSES ARE STUCK

```bash
ps aux | grep lean | grep -v grep
```

If any lean process is using >200MB and running for >1 hour, it is stuck in elaboration. You CANNOT kill it (it's from a prior session). IGNORE it. DO NOT run `lake build` on the full Wasm file — it will hang.

## STEP 1: Use lean_goal and lean_multi_attempt ONLY. No full builds.

## STEP 2: Close ONE sorry. Pick the EASIEST one.

### Target A: L6864 — `return (some t)`
- The `return none` case is FULLY PROVED above (L6822-6863). READ IT CAREFULLY.
- For `return (some t)`: the trivial `t` needs evaluation first
- Pattern: `ANF.step?_return_some` + `irStep?` for const + return
- A stuttering simulation template exists: `step_sim_return_litNull` at L6884
- This is a 1:N step (IR needs multiple steps for one ANF step)

### Target B: L6876 — `break label`
- Both ANF and IR produce error signals for break
- Should be simple: `ANF.step?_break` + `irStep?_break`

### Target C: L6879 — `continue label`
- Same pattern as break

### Target D: L6867 — `yield arg delegate`
- If yield is unsupported, it should error/trap on both sides

### Wasm sorry locations (18 total, verified 2026-03-29T11:05):
- L6798 (let), L6806 (seq), L6810 (if), L6813 (while), L6816 (throw), L6819 (tryCatch)
- L6864 (return some), L6867 (yield), L6870 (await), L6873 (labeled), L6876 (break), L6879 (continue)
- L10857 (call), L10912 (call stack underflow), L10916 (call success), L10919 (callIndirect)

## CONSTRAINTS
- DO NOT run `lake build VerifiedJS.Wasm.Semantics` — your stuck process will block it
- Use `lean_goal` and `lean_multi_attempt` for testing
- MAX 10 lines of new proof per attempt
- LOG to agents/wasmspec/log.md every 15 minutes
- If stuck >30 min on one sorry, move to next

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
