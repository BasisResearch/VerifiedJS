# jsspec — Close L3970 (FuncsSupported) then Core_step_preserves_supported leftovers

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

## REALITY CHECK: CC has 13 sorries. 10 of 13 are ARCHITECTURALLY BLOCKED.
The captured variable (L4202), CCStateAgree (L4531/4554/7371/7444/7552), semantic mismatch (L5326/5334), getIndex string (L5972), and tryCatch finally (L7372) cases ALL require multi-step simulation or CCState redesign. DO NOT waste time on them.

## CLOSEABLE TARGETS (in priority order)

### TASK 1: L3970 — closure.body.supported (in Core_step_preserves_supported)
Line 3970 in `Core_step_preserves_supported`, call case with closure.

**Context**: After Core.step? on `.call (.lit (.function idx)) argVals`, the result is a state with `expr := closure.body` where `closure = s.funcs[idx]`. Need to prove `closure.body.supported = true`.

**What you need**: A `FuncsSupported` invariant — all function bodies in `s.funcs` have `.supported = true`.

**Approach**:
1. Add hypothesis `(hfuncs_supp : ∀ i fd, s.funcs[i]? = some fd → fd.body.supported = true)` to the theorem
2. At L3970, use: `exact hfuncs_supp idx closure hfunc` (or similar)
3. Then at the call site (L4175), prove the hypothesis is satisfied — this requires proving FuncsSupported is preserved by steps (new funcs from functionDef have supported bodies if input was supported)
4. The initial FuncsSupported comes from the program being supported

**Alternative simpler approach**: If adding a hypothesis is too invasive, try:
1. `lean_goal` at L3970 to see exact state
2. Check if there's already a hypothesis about funcs in scope
3. Maybe `hsupp` (the supported hypothesis) implies it via the step structure

### TASK 2: L5118 — non-consoleLog function call (in closureConvert_step_simulation)
If Task 1 gives you a FuncsCorr-like invariant, use it to relate `sf.funcs[idx]` to `sc.funcs[idx]`.

### TASK 3: L7214 — functionDef case (only if Tasks 1-2 done)
Complex multi-step but maybe decomposable. Core creates closure, Flat creates makeClosure+makeEnv.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
