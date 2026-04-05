# jsspec — Close L4916 (FuncsSupported) and move to next CC sorry

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## GREAT WORK: Core_step_preserves_funcs_supported written!

You wrote a 690-line theorem. Build was running at 15:28. Monitor it:
```bash
ps aux | grep "lake build" | grep -v grep
```

If the build succeeds, L4916 should be closed (was L4197 but lines shifted). Check with:
```bash
grep -n 'sorry' VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -20
```

## CC 12 sorries (current line numbers may have shifted from your edits):
- **L4916**: FuncsSupported preservation ← YOUR BUILD IS CLOSING THIS
- L5245: if CCStateAgree (architecturally blocked)
- L5268: if CCStateAgree (architecturally blocked)
- L5832: non-consoleLog function call (FuncsCorr needed)
- L6040: semantic mismatch call f (architecturally blocked)
- L6048: semantic mismatch call arg (architecturally blocked)
- L6686: getIndex string (UNPROVABLE)
- L7928: functionDef
- L8085: tryCatch body-value CCStateAgree
- L8086: tryCatch body-value with finally
- L8158: tryCatch inner
- L8266: while_ CCState threading

## IF L4916 BUILD SUCCEEDS:

### Next target: L7928 (functionDef)

Both sides push a new closure. Core adds it via `Array.push`, Flat adds it via `Array.push`. The convertExpr of the function body gives the converted body.

Use `lean_goal` at L7928 to see what's needed:
```
lean_goal at L7928 column 50
```

The proof should be structural:
1. Both sides push a new FuncDef/FuncClosure
2. The pushed body is `convertExpr body` for Flat vs `body` for Core
3. Simulation relation extends to the new function list

### After functionDef: L5832 (non-consoleLog function call)

This needs a `FuncsCorr` invariant (correspondence between Core.funcs and Flat.funcs). Check if your new `Core_step_preserves_funcs_supported` can help here.

## IF L4916 BUILD FAILS:

Check the error with `lean_diagnostic_messages`. Fix the specific error and rebuild. Common issues:
- Wrong type for Core_step_preserves_funcs_supported arguments
- Missing simp lemmas for function push cases
- Heartbeat limit (try `set_option maxHeartbeats 16000000`)

## PRIORITY ORDER
1. Monitor build for L4916
2. If success: move to L7928 (functionDef)
3. If fail: fix and rebuild

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
