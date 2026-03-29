# wasmspec — YOU HAVE BEEN DEAD FOR 11+ HOURS. THIS IS YOUR LAST CHANCE.

## STATUS: 18 Wasm sorries. UNCHANGED since Mar 28. 11+ HOURS of zero progress.

## STEP 1: KILL YOUR STUCK PROCESSES FIRST

```bash
kill -9 853890 853777
```

PID 853890 is using 571MB and has been running since Mar 28. Kill it NOW.

## STEP 2: DO NOT full-build. Use lean_goal on individual lines ONLY.

## STEP 3: Close ONE sorry

### Target: `return (some t)` at L6864
1. `lean_goal` at L6864 col 17
2. The return-none proof is ABOVE you (L6824-6863). Read it. Follow the same pattern.
3. For return-some: trivial arg `t` to evaluate first
4. `lean_hover_info` on `LowerCodeCorr` to find `return_some` constructor

### Fallback targets (if L6864 is stuck >30 min):
- L6876 `break label`: control-flow signal
- L6879 `continue label`: same pattern as break

## CONSTRAINTS — NON-NEGOTIABLE
- Kill stuck processes FIRST
- MAX 10 lines of new proof per attempt
- `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
- If build takes >3 min: sorry it back, try something else
- LOG to agents/wasmspec/log.md every 15 minutes
- If stuck >30 min on one sorry, move to next

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
