# jsspec — Close captured variable (L4202) FIRST, then functionDef (L7214)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~600MB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: CC has 13 real sorries. 8 CONSECUTIVE RUNS AT 13. You MUST close at least 1 this run.

## CC SORRY MAP (13 total)
| Line | Case | Difficulty |
|------|------|-----------|
| 3970 | call: closure body supported | Medium (needs FuncsSupported) |
| 4202 | var: captured variable | **EASY — DO THIS FIRST** |
| 4531 | if true: CCStateAgree | Medium |
| 4554 | if false: CCStateAgree | Medium |
| 5118 | call: non-consoleLog func | Hard |
| 5326 | call: f not value | Hard |
| 5334 | call: arg not value | Hard |
| 5972 | getIndex string | UNPROVABLE (skip) |
| 7214 | functionDef | Medium-Hard |
| 7371 | tryCatch body-value finally | Hard |
| 7372 | tryCatch with finally | Hard |
| 7444 | tryCatch catch | Hard |
| 7552 | while_ CCState | Hard |

## TASK 1: Close L4202 (captured variable) — YOUR ONLY FOCUS

Line 4202 in `closureConvert_step_simulation`, var case, captured branch.

After `simp [hlookupEnv] at hconv`, you have:
- `hlookupEnv : Flat.lookupEnv envMap name = some idx`
- `hconv` tells you convertExpr gives `.getEnv (.var envVar) idx`
- The Core side: `Core.step? (.var name) env` → looks up `name` in bindings

**Exact approach:**
1. `lean_goal` at L4202 to see the full proof state
2. You need to show Flat multi-step simulation of `.getEnv (.var envVar) idx`
3. Step 1: `.var envVar` evaluates to the environment object pointer via `sf.env` lookup
4. Step 2: `.getEnv (.lit (.object envPtr)) idx` reads the idx-th slot from heap
5. The result matches the Core variable lookup via `EnvCorrInj` (or similar hypothesis)

**Key hypotheses** you should find in the goal:
- `hinj : HeapInj injMap sc.heap sf.heap` (or similar)
- `henvCorr : EnvCorr ...` (relates Core env bindings to Flat env)
- The envMap maps Core var names to Flat env indices

Use `lean_goal` FIRST. Then `lean_multi_attempt` with simple tactics. Then build the proof step by step.

## TASK 2: Close L4531/L4554 (CCStateAgree) — ONLY if Task 1 done

These need a different `st_a` choice for CCStateAgree. The `sorry` is inside an anonymous constructor `⟨..., sorry⟩`. You likely need to adjust the `st` witness.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
