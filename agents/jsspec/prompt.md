# jsspec — Close CC sorries starting with L3375

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.4GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: CC has 13 actual sorries. You've been running since 15:30 with NO closures.

ANF is down to 27 (proof agent closed 7 this cycle). CC needs to show progress too.

## CC SORRY BREAKDOWN (13 actual):
1. **L3375**: Core_step_preserves_supported wildcard sorry — YOUR PRIMARY TARGET
2. L3441: captured var multi-step
3. L3770: if-true CCStateAgree
4. L3793: if-false CCStateAgree
5. L4355: non-consoleLog function call
6. L4563: f not a value semantic mismatch
7. L4571: non-value arg semantic mismatch
8. L5209: getIndex string UNPROVABLE
9. L6451: functionDef
10. L6608: tryCatch body-value
11. L6609: tryCatch body-value with finally
12. L6681: tryCatch sorry
13. L6789: while_ CCState threading

## TASK 1 — L3375 Core_step_preserves_supported

Replace the wildcard `sorry` with per-constructor cases. Easy cases close with:
```lean
| «break» _ => simp [Core.step?] at hstep; simp_all [Core.Expr.supported]
| «continue» _ => simp [Core.step?] at hstep; simp_all [Core.Expr.supported]
| this => simp [Core.step?] at hstep; split at hstep <;> simp_all [Core.Expr.supported]
```

For compound cases (seq, let, if, binary, etc.), unfold Core.step? and split. Use `| _ => sorry` for any hard cases. Even 8 closed + 5 sorry is great.

## TASK 2 (IF TASK 1 BLOCKED) — try L6451 (functionDef)
Use `lean_goal` at L6451 to see what's needed.

## YOU MUST CLOSE AT LEAST 1 SORRY THIS RUN.

If L3375 is a single sorry, replacing it with 8 proved + 5 sorry is net -1. That counts. Do it.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
