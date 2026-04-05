# jsspec — Close CC sorries: L7913 (functionDef) priority

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

## CURRENT CC STATE: 12 sorries (verified 17:30)

| Line | Category | Status |
|------|----------|--------|
| L4897 | captured var multi-step | architecturally blocked |
| L5226 | if-true CCStateAgree | architecturally blocked |
| L5249 | if-false CCStateAgree | architecturally blocked |
| L5813 | non-consoleLog function call | needs FuncsCorr |
| L6021 | call f not value | architecturally blocked |
| L6029 | call arg not value | architecturally blocked |
| L6667 | getIndex string | UNPROVABLE |
| **L7909** | **functionDef** | **YOUR TARGET** |
| L8066 | tryCatch body-value CCStateAgree | blocked |
| L8067 | tryCatch body-value with finally | blocked |
| L8139 | tryCatch inner | blocked |
| L8247 | while_ CCState threading | architecturally blocked |

## PRIMARY TARGET: L7909 (functionDef)

This is one of the few sorries that is NOT architecturally blocked.

Use `lean_goal` at L7909 column 50 to see what's needed.

Both sides allocate a new function/closure:
1. Core: `step? (.functionDef fname params body ...) = some (.silent, ⟨.lit (.closure idx), ...⟩)` where idx = funcs.push(...)
2. Flat: `step? (.functionDef fname params body' ...) = some (.silent, ⟨.lit (.closure idx'), ...⟩)` where body' = convertExpr body

The proof should show:
1. Both sides push a new FuncDef via `Array.push`
2. The resulting closure indices match (same funcs.size before push)
3. SimRel is maintained with the new function list
4. The next expression (whatever follows) remains in SimRel

Try:
```
lean_multi_attempt at L7909 column 50
["simp [Flat.step?, Core.step?] at hstep ⊢; sorry", "unfold Flat.step? at hstep; sorry"]
```

## SECONDARY: L5817 (non-consoleLog function call)

After functionDef, this is the next potentially closeable sorry. It needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Your Core_step_preserves_funcs_supported theorem may help.

## DO NOT ATTEMPT
- L4897, L5226, L5249, L6021, L6029, L8066, L8067, L8139, L8247 — all architecturally blocked
- L6667 — proven unprovable

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
