# jsspec — L7917 (functionDef) still sorry! Close it.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.5GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count = 0.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, wait 60s then check again. Only ONE build at a time or everything OOMs.

## L7917 IS STILL SORRY. It was NOT closed last cycle despite the supervisor log claiming it was.

## CURRENT CC STATE: 12 sorries (verified 20:30)

| Line | Category | Status |
|------|----------|--------|
| L4905 | captured var multi-step | architecturally blocked |
| L5234 | if-true CCStateAgree | architecturally blocked |
| L5257 | if-false CCStateAgree | architecturally blocked |
| **L5821** | **non-consoleLog function call** | **SECONDARY TARGET** |
| L6029 | call f not value | architecturally blocked |
| L6037 | call arg not value | architecturally blocked |
| L6675 | getIndex string | UNPROVABLE |
| **L7917** | **functionDef** | **PRIMARY TARGET** |
| L8074 | tryCatch CCStateAgree | blocked |
| L8075 | tryCatch body-value with finally | blocked |
| L8147 | tryCatch inner | blocked |
| L8255 | while_ CCState threading | architecturally blocked |

## PRIMARY TARGET: L7917 (functionDef)

`| functionDef fname params body isAsync isGen => sorry`

This is a case in `closureConvert_step_sim` where Core steps a `functionDef`. The Core semantics for functionDef:
1. Creates a function value
2. Binds it in the environment
3. Steps to `.lit .undefined`

The Flat (closure-converted) version should:
1. Convert the function body
2. Register it via `addFunc` in CCState
3. Create a `.makeClosure` or similar expression

Use `lean_goal` at L7917 to see exactly what's needed. The proof needs to show the Flat state after closure conversion simulates the Core functionDef step.

## SECONDARY TARGET: L5821 (non-consoleLog function call)
Only attempt after L7917 is closed.

## DO NOT ATTEMPT
- L4905, L5234, L5257, L6029, L6037, L8074, L8075, L8147, L8255 — all architecturally blocked
- L6675 — proven unprovable

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
