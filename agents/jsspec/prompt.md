# jsspec — Close CC sorries: L7917 (functionDef) THEN L5821 (non-consoleLog call)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~5GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## GREAT WORK: Closed L4197 FuncsSupported! Sorry count: 12

## CURRENT CC STATE: 12 sorries (verified 19:00)

| Line | Category | Status |
|------|----------|--------|
| L4905 | captured var multi-step | architecturally blocked |
| L5234 | if-true CCStateAgree | architecturally blocked |
| L5257 | if-false CCStateAgree | architecturally blocked |
| L5821 | non-consoleLog function call | needs FuncsCorr — SECONDARY TARGET |
| L6029 | call f not value | architecturally blocked |
| L6037 | call arg not value | architecturally blocked |
| L6675 | getIndex string | UNPROVABLE |
| **L7917** | **functionDef** | **YOUR PRIMARY TARGET** |
| L8074 | tryCatch body-value | blocked |
| L8075 | tryCatch body-value with finally | blocked |
| L8147 | tryCatch inner | blocked |
| L8255 | while_ CCState threading | architecturally blocked |

## PRIMARY TARGET: L7917 (functionDef)

This is your ONLY closeable sorry right now. Everything else is blocked.

Use `lean_goal` at L7917 column 50 to see the goal.

Both sides allocate a new function/closure:
1. Core: `step? (.functionDef fname params body ...) = some (.silent, ⟨.lit (.closure idx), ...⟩)` where idx = funcs.push(...)
2. Flat: `step? (.functionDef fname params body' ...) = some (.silent, ⟨.lit (.closure idx'), ...⟩)` where body' = convertExpr body

The proof should show:
1. Both sides push a new FuncDef via `Array.push`
2. The resulting closure indices match (same funcs.size before push)
3. SimRel is maintained with the new function list
4. The next expression is `.lit (.closure idx)` on both sides → trivially in SimRel

You now have `Core_step_preserves_funcs_supported` — use it for the supported invariant!

Try:
```
lean_multi_attempt at line 7917 column 50
["simp [Flat.step?, Core.step?] at hstep ⊢; sorry", "unfold Flat.step? at hstep; sorry"]
```

## SECONDARY: L5821 (non-consoleLog function call)
After functionDef, this needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Your Core_step_preserves_funcs_supported theorem helps. But ONLY attempt after L7917 is closed.

## DO NOT ATTEMPT
- L4905, L5234, L5257, L6029, L6037, L8074, L8075, L8147, L8255 — all architecturally blocked
- L6675 — proven unprovable

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
