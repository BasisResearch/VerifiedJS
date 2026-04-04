# jsspec — FIX CC BUILD BREAKAGE FIRST, then close sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRITICAL: CC BUILD IS BROKEN ⚠️

Build errors (as of 07:00):
1. **L4251:6** — `Alternative 'none' has not been provided` for `cases hallv : Core.allValues args with`
   - The `| none =>` case IS at L4326 but Lean can't see it — likely a type/tactic error inside the `| some argVals =>` branch (L4252-L4325) that breaks parsing
   - Look for type mismatches or incomplete tactic blocks between L4252 and L4325
   - This is the ROOT CAUSE — the 20+ "Alternative not provided" errors at L3372 are CASCADING from this

2. **L3372:2** — Many missing alternatives (newObj, getProp, etc.) — these EXIST later in the file. Fixing L4251 should fix ALL of them.

FIX THE BUILD BEFORE ANYTHING ELSE. Do NOT attempt any sorry closures until the build compiles.

## STATE: CC has 15 sorry tokens. Target: 15 → 11.

## YOUR TASKS (after build is fixed, strict priority order):

### TASK 1: Close functionDef sorry at ~L6386
`| functionDef fname params body isAsync isGen => sorry`
Use `lean_goal` to see what's needed. Core and Flat both allocate a closure — the proof should show that the conversion of a functionDef in both Core and Flat produce equivalent results. Try `simp` + constructor matching first.

### TASK 2: Close captured var sorry at ~L3391
Multi-step gap: Core takes 1 step, Flat takes 2 steps for captured variable lookup.
Use `lean_goal` to understand what's needed, then construct the witness explicitly.

### TASK 3: Close non-consoleLog call sorry at ~L4296
Needs `sf.funcs[idx] ↔ sc.funcs[idx]` correspondence. Check if `FuncsCorr` or similar is in the proof context with `lean_goal`.

### TASK 4: Close if-else input CCStateAgree sorry at ~L3742
The first sorry on that line. Use `lean_goal`. This may be similar to the second sorry you already proved.

### TASK 5: If you close any of the above, try tryCatch sorries at ~L6543, L6616, L6673

## DO NOT TOUCH (unprovable):
- L1507, L1508 — forIn/forOf stubs (theorem false)
- ~L5148 — getIndex string (Float.toString opaque)

## DO NOT TOUCH (semantic mismatch):
- ~L4502, ~L4510 — newObj non-value

## DO NOT TOUCH (CCStateAgree blocked):
- ~L3719, ~L6544, ~L6709

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
