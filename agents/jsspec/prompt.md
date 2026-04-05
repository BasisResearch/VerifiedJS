# jsspec — Close captured variable (L4175) FIRST, then functionDef (L7187)

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

## STATUS: CC has 13 real sorries. You are reassigned from call.

## TASK 1: Close L4175 (captured variable) — DO THIS FIRST

Line 4175: `sorry` inside `closureConvert_step_simulation`, var case, captured branch.

Context: `lookupEnv envMap name = some idx`, so convertExpr gives `.getEnv (.var envVar) idx`.

**Core side**: `Core.step? (.var name) env` → looks up `name` in `env.bindings`, returns the value.

**Flat side**: `.getEnv (.var envVar) idx` needs multi-step simulation:
1. Step `.getEnv (.var envVar) idx` — first `.var envVar` evaluates to environment object pointer
2. `.getEnv (.lit (.object envPtr)) idx` — looks up idx-th value in heap object

**Key hypotheses you'll need**:
- `EnvCorrInj injMap sc.env sf.env` — relates Core env bindings to Flat env
- `HeapInj injMap sc.heap sf.heap` — heap correspondence
- The envMap maps Core variable names to Flat env indices

Steps:
1. `lean_goal` at L4175 to see exact proof state
2. Unfold Flat.step? for `.getEnv (.var envVar) idx`
3. Show `.var envVar` steps to the env object (via `sf.env` lookup)
4. Show getEnv on the object gives the right value (via HeapInj + EnvCorrInj)
5. Construct the multi-step simulation using Flat.Steps

## TASK 2: Close L7187 (functionDef) — ONLY if Task 1 is done

Line 7187: `| functionDef fname params body isAsync isGen => sorry`

This is complex (multi-step: makeEnv evaluates captured exprs, then makeClosure creates closure). Only attempt after Task 1.

**Core side** (L8594 Core/Semantics.lean): creates FuncClosure from params+body+env, pushes to funcs, result = `.lit (.function idx)`

**Flat side** (L231 Flat/ClosureConvert.lean): creates `(.makeClosure funcIdx (.makeEnv capturedExprs), st3)`

## TASK 3: L3960 (call) — ONLY if Tasks 1-2 are done

## PRIORITY ORDER
1. L4175 (captured variable) — most tractable, single variable lookup
2. L7187 (functionDef) — complex multi-step
3. L3960 (call) — only if time remains

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
