# jsspec — Close CC sorries: L7919 (functionDef) THEN L5823 (non-consoleLog call)

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

## !! SORRY COUNT WENT UP !!
CC went from 10 → 12 sorries. The tryCatch at old L8071 split into L8076 + L8077 (2 sorries). The if-false at L5259 reappeared. **Stop decomposing — start CLOSING.**

## CURRENT CC STATE: 12 sorries (verified 18:30)

| Line | Category | Status |
|------|----------|--------|
| L4907 | captured var multi-step | architecturally blocked |
| L5236 | if-true CCStateAgree | architecturally blocked |
| L5259 | if-false CCStateAgree | architecturally blocked |
| L5823 | non-consoleLog function call | needs FuncsCorr |
| L6031 | call f not value | architecturally blocked |
| L6039 | call arg not value | architecturally blocked |
| L6677 | getIndex string | UNPROVABLE |
| **L7919** | **functionDef** | **YOUR PRIMARY TARGET** |
| L8076 | tryCatch body-value | blocked |
| L8077 | tryCatch body-value with finally | blocked |
| L8149 | tryCatch inner | blocked |
| L8257 | while_ CCState threading | architecturally blocked |

## PRIMARY TARGET: L7919 (functionDef)

This is your ONLY closeable sorry right now. Everything else is blocked.

Use `lean_goal` at L7919 column 50 to see the goal.

Both sides allocate a new function/closure:
1. Core: `step? (.functionDef fname params body ...) = some (.silent, ⟨.lit (.closure idx), ...⟩)` where idx = funcs.push(...)
2. Flat: `step? (.functionDef fname params body' ...) = some (.silent, ⟨.lit (.closure idx'), ...⟩)` where body' = convertExpr body

The proof should show:
1. Both sides push a new FuncDef via `Array.push`
2. The resulting closure indices match (same funcs.size before push)
3. SimRel is maintained with the new function list
4. The next expression is `.lit (.closure idx)` on both sides → trivially in SimRel

Try:
```
lean_multi_attempt at line 7919 column 50
["simp [Flat.step?, Core.step?] at hstep ⊢; sorry", "unfold Flat.step? at hstep; sorry"]
```

## SECONDARY: L5823 (non-consoleLog function call)
After functionDef, this needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Your Core_step_preserves_funcs_supported theorem may help. But ONLY attempt after L7919 is closed.

## DO NOT ATTEMPT
- L4907, L5236, L5259, L6031, L6039, L8076, L8077, L8149, L8257 — all architecturally blocked
- L6677 — proven unprovable

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
