# wasmspec — Close captured-var + functionDef + tryCatch CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell)
- Check builds with: `pgrep -x lake` (not `-f`)
- **NEVER** use a `while` loop waiting for processes. Use a single `pgrep -x lake` check then proceed.

## MEMORY: 7.7GB total, NO swap.

## HNOERR SORRIES: BLOCKED — DO NOT ATTEMPT
All 22 hnoerr/hev_noerr sorries need Core Fix D. Skip them entirely.

## STATUS (19:05 Mar 30)
- CC: 44 sorries. 22 hnoerr (BLOCKED), 2 forIn/forOf (unprovable), **20 closable.**
- Your last run (14:30) applied hnoerr guards but has been stuck for 4.5 hours. Start fresh.

## YOUR TASK: Close non-hnoerr CC sorries. Target: ≥2.

### TARGET 1: Captured variable case (L3204) — HIGHEST PRIORITY

This is the `| some idx =>` branch: `.var name` where `lookupEnv envMap name = some idx`.
The converted expression is `.getEnv (.var envVar) idx`.

Steps:
1. `lean_goal` at L3204 to see the full proof state
2. The Core side does: `Core.step? {s | .var name}` → env lookup → value
3. The Flat side does: `Flat.step? {s | .getEnv (.var envVar) idx}` → gets closure env array from heap → gets element at idx
4. CC_SimRel relates: `envMap name = some idx` means `heap[closureEnvAddr][idx] = env[name]`
5. Use `lean_local_search "getEnv"` and `lean_local_search "EnvCorr"` to find relevant lemmas

### TARGET 2: functionDef (L5410) — MEDIUM PRIORITY

`| functionDef fname params body isAsync isGen => sorry`

1. `lean_goal` at L5410
2. Core.step? on functionDef creates a closure and binds it to fname
3. Flat.step? on the converted expression does the same with the converted body
4. CC_SimRel must hold: converted closure body relates to original, env extended

### TARGET 3: tryCatch (L5501) — MEDIUM PRIORITY

`| tryCatch body catchParam catchBody finally_ => sorry`

1. `lean_goal` at L5501
2. This is an expression-level case — tryCatch sets up a handler
3. Core.step? enters the try body; Flat.step? enters the converted try body
4. CC_SimRel must show converted body relates to original

### TARGET 4: newObj (L4066) — LOWER PRIORITY

`| newObj f args => sorry`

1. `lean_goal` at L4066
2. Similar to call — evaluate f and args, create new object

### TARGET 5: Begin Core Fix D staging (LOWEST PRIORITY, only if other targets closed)

If you close ≥2 sorries above, create `.lake/_tmp_fix/Core_fix_d_plan.md` documenting:
- Each position in Core/Semantics.lean that needs `.error msg` match arm
- The exact code change per position
- List of Core_step?_*_error companion theorems needed

## DO NOT TOUCH:
- ANFConvertCorrect.lean (proof agent owns this)
- hnoerr/hev_noerr sorries (BLOCKED)
- forIn/forOf stubs (unprovable)

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean`
3. Log to agents/wasmspec/log.md

## TARGET: Close at least 2 non-hnoerr sorries → CC from 44 to ≤42
