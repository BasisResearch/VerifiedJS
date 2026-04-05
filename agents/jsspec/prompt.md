# jsspec — STOP working on call. Close functionDef (L7119) NOW.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec are building ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: You have been stuck on call (L3921) for 6+ HOURS across multiple runs. STOP.

CC has 13 real sorries. You are reassigned.

## TASK 1: Close L7119 (functionDef) — DO THIS FIRST

Line 7119: `| functionDef fname params body isAsync isGen => sorry`

This is `closureConvert_step_simulation` for the functionDef case.

Steps:
1. `lean_goal` at line 7119 to see exact proof state
2. Core.step? for functionDef allocates a closure on the heap and binds the name
3. Flat.convertExpr for functionDef creates a makeClosure + let binding
4. Show the Flat side can step to match

Key context: look at how other cases in this theorem are proved (e.g., `throw` at L7120-7139). Follow the same pattern:
- Extract conversion info from hconv
- Show sf has the right form
- Show Flat.step? matches
- Build the output SimRel

## TASK 2: Close L4107 (captured variable)

Line 4107: captured variable case in `closureConvert_step_simulation`.

When `lookupEnv envMap name = some idx`, convertExpr gives `.getEnv (.var envVar) idx`.
The Core side does `env.lookup name = some v`. The Flat side needs to:
1. Step `.getEnv (.var envVar) idx` — first step looks up envVar in env
2. Second step does getEnv on the closure environment

Use `lean_goal` at L4107 to see what you need. The `EnvCorr` hypothesis should give you the value correspondence.

## TASK 3: L3921 (call) — ONLY if Tasks 1-2 are done

Leave call for last. It requires FuncsSupported invariant changes.

## PRIORITY ORDER
1. L7119 (functionDef) — freshest target, highest chance of closure
2. L4107 (captured variable) — captured env lookup
3. L3921 (call) — only if time remains

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
