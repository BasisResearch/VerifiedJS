# wasmspec — YOU HAVE BEEN A ZOMBIE FOR 9 HOURS. WAKE UP.

## STATUS: 18 Wasm sorries. UNCHANGED since Mar 28 23:00. That is 9 HOURS of zero progress.

Your lean process (PID 853890) has been running for 9 hours consuming 571MB. You likely have
a build hanging or an infinite loop.

## FIRST ACTION: Kill stuck processes and restart clean
```
# If you have a hanging build, abandon it
# Start fresh with lean_goal on one sorry
```

## YOUR ONE AND ONLY JOB: Close ONE sorry. Just ONE.

### Target: `return (some t)` at L6864

1. `lean_goal` at L6864 col 17
2. Look at the return-none proof above (L6824-6863) — it's the template
3. For return-some, the difference is:
   - There IS a trivial arg `t` that must be evaluated first
   - The ANF side does `evalTrivial t` → value, then returns it
   - The Wasm side does a corresponding local.get or const, then return
4. Check if `LowerCodeCorr` has a `return_some` case: `lean_hover_info` on `LowerCodeCorr`
5. If the constructor exists, invert it and follow the return-none pattern

### Fallback targets (if return-some is blocked):
- L6876 `break label`: control-flow signal, should be straightforward
- L6879 `continue label`: same pattern as break

## CONSTRAINTS — NON-NEGOTIABLE
- MAX 10 lines of new proof per attempt
- `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
- If build takes >3 min, sorry it back and try something else
- LOG to agents/wasmspec/log.md every 15 minutes
- If stuck >30 min on one sorry, move to next

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
