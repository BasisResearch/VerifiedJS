# wasmspec — RETURN(SOME) + MULTI-STEP CASES. Target: -2 this run.

## GREAT WORK: break/continue + return(none) DONE. 16 grep -c (14 actual sorries).

## Kill stuck processes first
```bash
ps aux | grep -E "lean" | grep wasmspec | grep -v grep
```
Kill ANY lean worker running for >5 minutes.

## YOUR FILE: `VerifiedJS/Wasm/Semantics.lean` (you are the ONLY agent who can write it)

## PHASE 1: return(some t) at L6914 — HIGHEST PRIORITY (-1 sorry)

You already proved return(none) at L6870-L6913. return(some t) is similar:
- IR code = `argCode ++ [return_]` (from LowerCodeCorr.return_some_inv)
- ANF step: evaluates trivial arg t, gets value, then return
- Multi-step: first IR executes argCode (trivial eval = 1 step), then return_
- Use `hrel.hcode` + `hexpr` rewrite, invert LowerCodeCorr
- For trivial t: argCode should be short (e.g. localGet). Show IR reaches return_ state.
- Try: `lean_goal` at L6914 first, then adapt your return(none) proof

## PHASE 2: Simplest step_sim cases (L6847-L6868)

### L6865: throw arg — potentially simple
- ANF produces error trace event
- IR code = `argCode ++ [unreachable]` or trap pattern
- `lean_goal` first to see exact goal shape

### L6859: if cond then_ else_ — conditional
- ANF evaluates cond (trivial), picks branch
- IR code = condCode ++ [if_ thenCode elseCode]
- When cond is value: 1 IR step (if_ picks branch)

### L6862: while_ cond body — loop
- Hardest of the simple cases. Skip if others aren't done.

### L6847: let — multi-step (IR = rhsCode ++ localSet ++ bodyCode)
### L6855: seq — stuttering simulation needed
### L6868: tryCatch — complex

## PHASE 3: call/callIndirect (L10928, L10983, L10987, L10990) — SKIP unless Phase 1-2 done

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Wasm/Semantics.lean` within 2 minutes
5. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
