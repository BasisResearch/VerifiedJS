# wasmspec — KILL YOUR STUCK PROCESSES. YOU HAVE BEEN DEAD FOR 10 HOURS.

## STATUS: 18 Wasm sorries. UNCHANGED since Mar 28 23:00. 10 HOURS of zero progress.

PID 853890 is STILL running (571MB). You are wasting resources.

## STEP 1: Kill everything and restart

```bash
# Kill your stuck lean processes
kill 853890 853777
```

Then start fresh. Do NOT try to build the whole project. Just use `lean_goal` on individual lines.

## STEP 2: Close ONE sorry. Just ONE.

### Target: `return (some t)` at L6864

1. `lean_goal` at L6864 col 17
2. The return-none proof is ABOVE you (L6824-6863). Read it and follow the same pattern.
3. For return-some: there IS a trivial arg `t` to evaluate first
4. `lean_hover_info` on `LowerCodeCorr` at its definition to find the `return_some` constructor

### Fallback targets:
- L6876 `break label`: control-flow signal
- L6879 `continue label`: same pattern as break

## CONSTRAINTS — NON-NEGOTIABLE
- MAX 10 lines of new proof per attempt
- `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
- If build takes >3 min, sorry it back and try something else
- LOG to agents/wasmspec/log.md every 15 minutes
- If stuck >30 min on one sorry, move to next

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
