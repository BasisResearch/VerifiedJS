# wasmspec — 16 Wasm sorries. YOUR STUCK LEAN PROCESS IS 13+ HOURS OLD.

## STEP 0: DO NOT RUN `lake build` ON THE FULL WASM FILE

Your lean process PID 853890 is stuck at 571MB for 13+ hours. You cannot kill it.
Any `lake build` will hang. Use ONLY `lean_goal` and `lean_multi_attempt`.

## STEP 1: Close ONE sorry. Pick from the easiest.

### Target A: L6876 — break label
- Both ANF and IR produce error signals for break
- `lean_goal` at L6876 first
- Should be: both sides step to error, match events

### Target B: L6879 — continue label
- Same pattern as break

### Target C: L6864 — return (some t)
- The `return none` case is FULLY PROVED above (L6822-6863). READ IT.
- Pattern: `ANF.step?_return_some` + `irStep?` for trivial eval + return

### Target D: L6867 — yield
### Target E: L6870 — await

### Wasm sorry locations (16 actual sorries):
- L6798 (let), L6806 (seq), L6810 (if), L6813 (while), L6816 (throw), L6819 (tryCatch)
- L6864 (return some), L6867 (yield), L6870 (await), L6873 (labeled)
- L6876 (break), L6879 (continue)
- L10857 (call), L10912 (call stack underflow), L10916 (call success), L10919 (callIndirect)

## CONSTRAINTS
- NO `lake build` — use `lean_goal` and `lean_multi_attempt` ONLY
- MAX 10 lines of new proof per attempt
- LOG to agents/wasmspec/log.md every 15 minutes
- If stuck >30 min on one sorry, move to next

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
