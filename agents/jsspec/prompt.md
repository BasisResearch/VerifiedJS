# jsspec — L3970 CLOSED! Now close L4203 (HeapInj staging) and L5119 (non-consoleLog call)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.5GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: CC now 12 sorries. L3970 CLOSED (great work!). objectLit/arrayLit FIXED.

## CC 12 sorries remaining:
- L4203: HeapInj refactor staging sorry
- L4532, L4555: if CCStateAgree (architecturally blocked)
- L5119: non-consoleLog function call (FuncsCorr needed)
- L5327, L5335: semantic mismatch call (architecturally blocked)
- L5973: getIndex string (UNPROVABLE)
- L7215: functionDef
- L7372, L7373: tryCatch CCStateAgree (architecturally blocked)
- L7445: tryCatch inner
- L7553: while_ CCState threading (architecturally blocked)

### TASK 1: L4203 — HeapInj staging sorry (PRIORITY 1)
This is in `closureConvert_step_simulation` at L4139. The comment says it was "temporarily sorry'd during HeapInj refactor" and "will be restored with HeapInj types."

**Strategy**:
1. `lean_goal` at L4203 to see what's needed
2. The proof was working before the HeapInj refactor — check git history for the old proof
3. The new proof needs `injMap` threading through ~30 cases
4. This is likely a LARGE sorry that covers the entire closureConvert_step_simulation body
5. If it's the main proof body, focus on the cases that have the clearest path

### TASK 2: L5119 — non-consoleLog function call (FuncsCorr)
```lean
sorry -- non-consoleLog function call: needs sf.funcs[idx] ↔ sc.funcs[idx] correspondence
```
**Strategy**:
1. `lean_goal` at L5119
2. Need: if `sf.funcs[idx]? = some fd_flat` then `sc.funcs[idx]? = some fd_core` with body correspondence
3. Check if CC_SimRel already has a FuncsCorr component, or if you need to add one
4. The FuncsSupported invariant pattern (from L3464) is a good model

### TASK 3: L7215 — functionDef case
```lean
| functionDef fname params body isAsync isGen => sorry
```
1. `lean_goal` at L7215
2. functionDef adds a new closure to s.funcs
3. Need to show Flat closureConvert of functionDef matches Core functionDef step
4. May need CCState updates for the new function

## ARCHITECTURALLY BLOCKED (DO NOT TOUCH)
- L4532/4555: CCStateAgree if-branches
- L5327/5335: semantic mismatch (Core allocates vs Flat steps)
- L5973: UNPROVABLE getIndex string
- L7372/7373: tryCatch CCStateAgree
- L7445: tryCatch inner
- L7553: while_ CCState threading

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
