# jsspec — Close CC sorries: L3375 first, then L6451 or L3441

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.9GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: CC has 13 actual sorries. You've been running 2+ HOURS with ZERO closures this cycle.

You MUST close at least 1 sorry or you will be replaced.

## CC SORRY BREAKDOWN (13):
1. **L3375**: Core_step_preserves_supported — PRIMARY TARGET
2. L3441: captured var multi-step
3. L3770: if-true CCStateAgree
4. L3793: if-false CCStateAgree
5. L4355: non-consoleLog function call
6. L4563: f not a value semantic mismatch
7. L4571: non-value arg semantic mismatch
8. L5209: getIndex string UNPROVABLE (skip this)
9. L6451: functionDef
10. L6608: tryCatch body-value
11. L6609: tryCatch with finally
12. L6681: tryCatch sorry
13. L6789: while_ CCState

## TASK 1 — L3375 Core_step_preserves_supported

This is a SINGLE sorry covering ALL cases. Replace with per-constructor splits.

**STEP BY STEP:**
1. Use `lean_goal` at L3375 to see the exact goal
2. Delete the `sorry` and write:
```lean
cases hstep : ... with  -- or match on the expression constructor
| lit => ...
| var => ...
```
3. Easy cases (lit, var, this, break, continue) close with `simp [Core.step?] at hstep; simp_all [Core.Expr.supported]`
4. For HARD cases, leave `sorry`. Even 8 closed + 5 sorry'd is a net win.

## TASK 2 — L6451 (functionDef)
If L3375 is blocked:
1. `lean_goal` at L6451
2. functionDef should involve `Flat.convertExpr` on the function body
3. The proof likely needs to show CCStateAgree is preserved through function allocation

## TASK 3 — L3441 (captured var multi-step)
If both above are blocked:
1. `lean_goal` at L3441
2. This involves proving captured variables are preserved through multiple steps

## YOU HAVE BEEN RUNNING 2+ HOURS. PRODUCE CODE CHANGES NOW.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
