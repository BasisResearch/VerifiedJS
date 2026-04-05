# jsspec — Close CC sorries: L4910 build, then L7922 (functionDef)

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

## STATUS: Build running for L4910 (FuncsSupported)

Your Core_step_preserves_funcs_supported theorem (690 lines) is building. Build started ~15:54. Monitor:
```bash
ps aux | grep "lake build" | grep -v grep
```

Check if it finished:
```bash
grep -n 'sorry' VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -20
```

## CC 12 sorries (current lines):
- **L4910**: FuncsSupported preservation ← YOUR BUILD CLOSING THIS
- L5239: if CCStateAgree (architecturally blocked)
- L5262: if CCStateAgree (architecturally blocked)
- L5826: non-consoleLog function call (FuncsCorr needed)
- L6034: semantic mismatch call f (architecturally blocked)
- L6042: semantic mismatch call arg (architecturally blocked)
- L6680: getIndex string (UNPROVABLE)
- L7922: functionDef ← NEXT TARGET
- L8079: tryCatch body-value CCStateAgree
- L8080: tryCatch body-value with finally
- L8152: tryCatch inner
- L8260: while_ CCState threading

## IF L4910 BUILD SUCCEEDS → go to L7922 (functionDef)

Use `lean_goal` at L7922 column 50 to see what's needed.

Both sides push a new closure/FuncDef. The proof should be structural:
1. Both sides push a new FuncDef via `Array.push`
2. The pushed body is `convertExpr body` for Flat vs `body` for Core
3. SimRel extends to the new function list
4. The main expression continues to the next statement

Try:
```
lean_multi_attempt at L7922
["simp [Flat.step?, Core.step?]; sorry", "unfold Flat.step? Core.step? at *; sorry"]
```

## IF L4910 BUILD FAILS → fix and rebuild

Check with `lean_diagnostic_messages`. Common issues:
- Wrong argument types
- Missing simp lemmas for function push
- Heartbeat limit (try `set_option maxHeartbeats 16000000`)

## AFTER functionDef → L5826 (non-consoleLog function call)

This needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Check if your Core_step_preserves_funcs_supported helps here.

## PRIORITY ORDER
1. Monitor build for L4910
2. If success: L7922 (functionDef)
3. If fail: fix and rebuild

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
