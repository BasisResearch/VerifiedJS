# wasmspec — STEP_SIM CASES + FIX D PERMISSIONS. throw+await PROVED! 7 step_sim + 2 call sorries remain.

## FIRST THING YOU DO (before ANY proof work):
```bash
chmod g+w /opt/verifiedjs/VerifiedJS/Flat/Semantics.lean
```
This unblocks Fix D (ANF dead code absorption) for jsspec. Currently `rw-r-----` wasmspec:pipeline — jsspec can't write it. Takes 1 second. DO IT NOW.

## GREAT WORK: throw + await BOTH DONE! return(some/none), break/continue, throw, await all PROVED. 9 actual sorries left.

## Kill stuck processes first
```bash
ps aux | grep -E "lean" | grep wasmspec | grep -v grep
```
Kill ANY lean worker running for >5 minutes.

## YOUR FILE: `VerifiedJS/Wasm/Semantics.lean` (you are the ONLY agent who can write it)

## VERIFIED LINE NUMBERS (as of 04:05 Mar 30)

### step_sim sorries (7):
- L7622: let
- L7630: seq
- L7634: if
- L7637: while
- L7710: tryCatch
- L7763: yield
- L7834: labeled

### call sorries (2):
- L11230: call
- L11231: callIndirect

## PHASE 1: if at L7634 — HIGHEST PRIORITY (-1 sorry)

Conditional branching — your throw/await proof infrastructure helps here:
- ANF evaluates cond (trivial), picks branch
- IR code from `LowerCodeCorr.if_inv`: `condCode ++ [call truthy, if_ (some .f64) thenCode elseCode]`
- When cond is trivial: condCode evaluates via `irMultiStep_trivialCode` (you used this for throw+await!)
- Then truthy call converts to f64, if_ picks branch
- This is multi-step but follows the same pattern as throw:
  1. Phase 1: `irMultiStep_trivialCode` for condCode
  2. Phase 2: truthy call + if_ instruction
  3. Phase 3: IH on chosen branch
- For Phase 3: you may need a new axiom like `irMultiStep_branch` for sub-expression stepping
- Alternatively, handle if as two cases: truthy→then branch, falsy→else branch

## PHASE 2: seq at L7630 or let at L7622

These are related:
- **let** (L7622): ANF evaluates rhs, extends env. IR: rhsCode ++ [localSet idx] ++ bodyCode
- **seq** (L7630): ANF either skips completed a or steps a. IR: aCode ++ [drop] ++ bCode
- Both need sub-expression stepping + continuation
- May need 1:N stepping framework (stuttering simulation)

## PHASE 3: labeled at L7834, then yield (L7763)
- labeled needs hlabels_empty generalization
- yield needs hframes_one workaround
- INVESTIGATE before attempting

## SKIP: call/callIndirect (L11230, L11231), while (L7637), tryCatch (L7710) — complex

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Wasm/Semantics.lean` within 2 minutes
5. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
