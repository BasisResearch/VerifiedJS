# jsspec — GREAT: L7917 closed! Next: L5821 (non-consoleLog call)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.3GB available. VERY TIGHT.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count = 0.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, wait 60s then check again. Only ONE build at a time or everything OOMs.

## EXCELLENT WORK: Closed L7917 (functionDef)! Sorry count: 11 (down from 12)

## CURRENT CC STATE: 11 sorries (verified 20:05)

| Line | Category | Status |
|------|----------|--------|
| L4905 | captured var multi-step | architecturally blocked |
| L5234 | if-true CCStateAgree | architecturally blocked |
| L5257 | if-false CCStateAgree | architecturally blocked |
| **L5821** | **non-consoleLog function call** | **YOUR PRIMARY TARGET** |
| L6029 | call f not value | architecturally blocked |
| L6037 | call arg not value | architecturally blocked |
| L6675 | getIndex string | UNPROVABLE |
| L8075 | tryCatch body-value | blocked |
| L8076 | tryCatch body-value with finally | blocked |
| L8148 | tryCatch inner | blocked |
| L8256 | while_ CCState threading | architecturally blocked |

## PRIMARY TARGET: L5821 (non-consoleLog function call)

This needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence from SimRel.

You have `Core_step_preserves_funcs_supported` from last cycle. The key is:
1. The SimRel should contain a funcs correspondence: `∀ i, sf.funcs[i]? = some fd_flat ↔ sc.funcs[i]? = some fd_core ∧ fd_flat = convertFuncDef fd_core`
2. When Core steps `call idx`, it looks up `sc.funcs[idx]`. Flat steps `call idx` and looks up `sf.funcs[idx]`.
3. Show the function bodies are related by `convertExpr` and the resulting states maintain SimRel.

Use `lean_goal` at L5821 to see exactly what's needed. Then `lean_multi_attempt` to test approaches.

## DO NOT ATTEMPT
- L4905, L5234, L5257, L6029, L6037, L8075, L8076, L8148, L8256 — all architecturally blocked
- L6675 — proven unprovable

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
