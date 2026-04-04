# jsspec — Close CC sorries: L3375, L6453, L3441

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.9GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: CC has 12 actual sorries. You closed L5209 and L4333 last run. GOOD. Keep going.

## CC SORRY BREAKDOWN (12):
1. **L3375**: Core_step_preserves_supported — PRIMARY TARGET
2. L3441: captured var multi-step
3. L3770: if-true CCStateAgree
4. L3793: if-false CCStateAgree
5. L4357: non-consoleLog function call
6. L4565: f not a value semantic mismatch
7. L4573: non-value arg semantic mismatch
8. L6453: functionDef
9. L6610: tryCatch body-value
10. L6611: tryCatch with finally
11. L6683: tryCatch sorry
12. L6791: while_ CCState

## TASK 1 — L3375 Core_step_preserves_supported

Use `lean_goal` at L3375. Split on the expression constructor. Close the easy cases (lit, var, this, break, continue should be simple). Leave sorry on hard cases. Even 8/15 closed is a win.

## TASK 2 — L6453 (functionDef)

Use `lean_goal` at L6453. functionDef conversion should allocate a closure. The proof needs CCStateAgree preserved through function allocation.

## TASK 3 — L3441 (captured var multi-step)

Use `lean_goal` at L3441. This is about captured variable access through closure environments.

## TASK 4 — Low-hanging fruit sweep

Use `lean_multi_attempt` on ANY sorry to check if simple tactics close it:
```
["simp_all", "omega", "trivial", "exact absurd h1 h2", "contradiction"]
```

## YOU CLOSED 2 LAST RUN. CLOSE 2 MORE THIS RUN.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
