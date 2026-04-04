# jsspec — CC is mostly blocked. Close L6616, then explore architecture fixes.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## GREAT JOB closing L6673 last run. CC is now at 14 sorries.

## STATE: CC has 14 sorry tokens. Most are architecturally blocked.

### Sorry classification:
- **Unprovable (2)**: L1507, L1508 (forIn/forOf stubs) — DO NOT TOUCH
- **Unprovable (1)**: L5148 (getIndex string) — DO NOT TOUCH
- **Semantic mismatch (2)**: L4502, L4510 (newObj non-value) — DO NOT TOUCH
- **CCStateAgree blocked (5)**: L3719, L3742, L6543, L6544, L6724 — cannot close without architecture change
- **HeapInj blocked (1)**: L6386 (functionDef) — cannot close without HeapInj extension
- **FuncsCorr blocked (1)**: L4296 (non-consoleLog call) — cannot close without FuncsCorr invariant
- **Multi-step blocked (1)**: L3391 (captured var) — 2 vs 1 step mismatch
- **Potentially actionable (1)**: L6616 (tryCatch body-error with finally)

## YOUR TASKS

### TASK 1: Close L6616 (tryCatch body-error CCStateAgree)

L6616 is similar to L6673 which you just closed. Use `lean_goal` at L6616 to see the exact goal. The pattern from L6673: thread IH's CCStateAgree through tryCatch sub-conversions using `convertExpr_state_determined`.

### TASK 2: If L6616 is blocked, investigate FuncsCorr for L4296

L4296 (non-consoleLog call) needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Check if any existing invariant (HeapInj, EnvCorr, etc.) covers function table correspondence. If not, see if adding a `FuncsCorr` field to the simulation relation is feasible. Use `lean_local_search` for `FuncsCorr`, `funcs`, `FuncDef`.

### TASK 3: If T1-T2 are blocked, investigate multi-step sim for L3391

L3391 (captured var) needs Flat to take 2 steps (getEnv var lookup + value) where Core takes 1 step (direct var lookup). Consider adding a `Flat.Steps` witness with 2 steps. Use `lean_goal` at L3391 to see what's needed.

### TASK 4: Architecture analysis for CCStateAgree

5 sorries are blocked by CCStateAgree. The root cause: converting both branches of if/while allocates fresh IDs, but only one branch executes. Write a short analysis (< 20 lines) in agents/jsspec/log.md about whether:
1. Making variable naming position-based (instead of counter-based) is feasible
2. Or adding a "both-branch-deterministic" lemma is feasible
This is ANALYSIS ONLY — do not change architecture without supervisor approval.

## DO NOT:
- Touch L1507, L1508, L5148, L4502, L4510
- Make architectural changes without clear plan
- Edit ANFConvertCorrect.lean

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
