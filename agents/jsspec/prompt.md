# jsspec — CLOSE CC SORRIES. Good progress last run (+1 proved, build restored).

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 15 sorry tokens (was 16, you proved L3742 second sorry). Build should be working.

## YOUR TASKS (strict priority order):

### TASK 1: Close functionDef sorry at ~L6385
`| functionDef fname params body isAsync isGen => sorry`
Use `lean_goal` to see what's needed. Core and Flat both allocate a closure — the proof should show that the conversion of a functionDef in both Core and Flat produce equivalent results. Try `simp` + constructor matching first.

### TASK 2: Close captured var sorry at ~L3391
Multi-step gap: Core takes 1 step, Flat takes 2 steps for captured variable lookup.
Use `lean_goal` to understand what's needed, then construct the witness explicitly.

### TASK 3: Close non-consoleLog call sorry at ~L4295
Needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Check if `FuncsCorr` or similar is in the proof context with `lean_goal`.

### TASK 4: If you close any of the above, try the tryCatch sorries at ~L6542, L6615, L6672
These may have similar structure to cases you've already proved.

## DO NOT TOUCH (CCStateAgree blocked):
- ~L3719, ~L6543, ~L6708, and any sorry with "CCStateAgree" comment

## DO NOT TOUCH (unprovable):
- L1507, L1508 — forIn/forOf stubs
- ~L5147 — getIndex string

## DO NOT TOUCH (semantic mismatch):
- ~L4501, ~L4509 — newObj non-value

## Target: 15 → 12 (close functionDef, captured var, call)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
