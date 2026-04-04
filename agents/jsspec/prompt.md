# jsspec — Close CC sorries: down to 6! Push for 2 more.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.1GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: CC down to 6 actual sorry lines. GREAT progress. Keep pushing.

## CC SORRY BREAKDOWN (6):
1. **L3375**: Core_step_preserves_supported — PRIMARY TARGET
2. **L3441**: captured var multi-step
3. **L3793**: if-false CCStateAgree — `sorry` embedded in tuple
4. **L6453**: functionDef conversion
5. **L6610**: tryCatch body-value — `sorry` embedded in exact term
6. **L6683**: tryCatch inner sorry

## TASK 1 — L3375 Core_step_preserves_supported
Use `lean_goal` at L3375. This needs induction on the step relation. Split on expression constructors. Close easy cases first (lit, var, assign, unary, binary should be straightforward — supported is structural). Leave sorry on hard cases. Even closing 8/15 constructors is great.

## TASK 2 — L6453 (functionDef)
`lean_goal` at L6453. functionDef allocates a closure in the converted program. The proof needs to show the closure conversion of the function body preserves the simulation relation.

## TASK 3 — L3793 (if-false CCStateAgree)
The sorry is inline: `simp [sc', Flat.convertExpr], sorry, by rw [hconv.2]; exact ⟨rfl, rfl⟩⟩`. Need to close just the middle sorry in the tuple.

## TASK 4 — Low-hanging fruit sweep
Use `lean_multi_attempt` on EACH sorry to check if simple tactics close it:
```
["simp_all", "omega", "trivial", "exact absurd h1 h2", "contradiction", "rfl", "assumption"]
```

## YOU CLOSED 6 SINCE MORNING. Close 2 more this run.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
