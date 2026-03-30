# wasmspec — STEP_SIM CASES. throw PROVED! 8 step_sim + 2 call sorries remain. Target: -1 this run.

## GREAT WORK: throw is DONE! return(some/none), break/continue, throw all PROVED. 10 actual sorries left.

## Kill stuck processes first
```bash
ps aux | grep -E "lean" | grep wasmspec | grep -v grep
```
Kill ANY lean worker running for >5 minutes.

## YOUR FILE: `VerifiedJS/Wasm/Semantics.lean` (you are the ONLY agent who can write it)

## VERIFIED LINE NUMBERS (as of 03:05 Mar 30)

### step_sim sorries (8):
- L7622: let
- L7630: seq
- L7634: if
- L7637: while
- L7702: tryCatch
- L7755: yield
- L7758: await
- L7761: labeled

### call sorries (2):
- L11157: call
- L11158: callIndirect

## PHASE 1: if at L7634 — HIGHEST PRIORITY (-1 sorry)

Conditional branching — your throw proof infrastructure should help here:
- ANF evaluates cond (trivial), picks branch
- IR code from `LowerCodeCorr.if_inv`: `condCode ++ [call truthy, if_ (some .f64) thenCode elseCode]`
- When cond is trivial: condCode evaluates via `irMultiStep_trivialCode` (you used this for throw!)
- Then truthy call converts to f64, if_ picks branch
- This is multi-step but follows the same pattern as throw:
  1. Phase 1: `irMultiStep_trivialCode` for condCode
  2. Phase 2: truthy call + if_ instruction
- Try reusing the throw proof structure

## PHASE 2: seq at L7630 or let at L7622

These are related:
- **let** (L7622): ANF evaluates rhs, extends env. IR: rhsCode ++ [localSet idx] ++ bodyCode
- **seq** (L7630): ANF either skips completed a or steps a. IR: aCode ++ [drop] ++ bCode
- Both need sub-expression stepping + continuation
- May need 1:N stepping framework (stuttering simulation)

## PHASE 3: labeled at L7761, then yield/await (L7755/L7758)
- labeled needs hlabels_empty generalization
- yield/await need hframes_one workaround
- INVESTIGATE before attempting

## SKIP: call/callIndirect (L11157, L11158) — blocked on hframes_one

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Wasm/Semantics.lean` within 2 minutes
5. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
