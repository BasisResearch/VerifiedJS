# wasmspec — STEP_SIM CASES. 9 step_sim + 2 call sorries remain. Target: -2 this run.

## GREAT WORK: return(some) DONE! 11 actual sorries remain (9 step_sim + call + callIndirect).

## Kill stuck processes first
```bash
ps aux | grep -E "lean" | grep wasmspec | grep -v grep
```
Kill ANY lean worker running for >5 minutes.

## YOUR FILE: `VerifiedJS/Wasm/Semantics.lean` (you are the ONLY agent who can write it)

## PHASE 1: throw at L7509 — HIGHEST PRIORITY (-1 sorry)

Throw is one of the simpler step_sim cases:
- ANF step: evaluates trivial arg, produces (.error msg) event
- IR code from `LowerCodeCorr.throw_inv`: `argCode ++ [unreachable]`
- For trivial arg: argCode is short (e.g. localGet), evaluates to 1 IR step
- Then `unreachable` instruction traps
- Trace alignment: ANF .error vs IR .trap — need `traceFromCore` alignment
- Try: `lean_goal` at L7509 first, then adapt the return(none) proof pattern

## PHASE 2: if at L7503 — conditional branching

- ANF evaluates cond (trivial), picks branch
- IR code from `LowerCodeCorr.if_inv`: `condCode ++ [call truthy, if_ (some .f64) thenCode elseCode]`
- When cond is trivial: condCode is short, gets value on stack
- Then truthy call converts to f64, if_ picks branch
- This is multi-step (3+ IR instructions for 1 ANF step)
- May need stuttering — check if step_sim_stutter framework exists

## PHASE 3: labeled at L7569, then yield/await (L7563/L7566)

### labeled — needs hlabels_empty workaround
- IR code: block with label push. Post-step state has non-empty labels → violates hlabels_empty
- May need LowerSimRel generalization (allow non-empty labels for labeled blocks)
- INVESTIGATE before attempting

### yield/await — need hframes_one workaround
- IR code includes `.call runtimeFunc` → pushes frame → violates hframes_one
- Same class of structural blocker

## SKIP: call/callIndirect (L10964, L11026) — blocked on hframes_one

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Wasm/Semantics.lean` within 2 minutes
5. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
