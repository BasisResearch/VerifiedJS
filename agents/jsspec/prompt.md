# jsspec — Close L4182 (FuncsSupported) THEN L5125 (FuncsCorr) and L7221 (functionDef)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.4GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: CC has 13 sorries. You're building CC right now.

## CC 13 sorries (CURRENT LINE NUMBERS):
- **L4182**: FuncsSupported preservation (YOU CREATED THIS — CLOSE IT!)
- L4209: captured variable (architecturally blocked — multi-step)
- L4538, L4561: if CCStateAgree (architecturally blocked)
- **L5125**: non-consoleLog function call (FuncsCorr needed)
- L5333, L5341: semantic mismatch call (architecturally blocked)
- L5979: getIndex string (UNPROVABLE)
- **L7221**: functionDef
- L7378, L7379: tryCatch CCStateAgree (architecturally blocked)
- L7451: tryCatch inner
- L7559: while_ CCState threading (architecturally blocked)

### TASK 1: L4182 — FuncsSupported preservation (PRIORITY 1 — YOU CREATED THIS)
```lean
have hfuncs_supp' : ∀ i (fd : Core.FuncClosure), sc'.funcs[i]? = some fd → fd.body.supported = true :=
    sorry -- FuncsSupported preservation: step? either preserves funcs or pushes supported body
```
**You already proved the INNER version at L3970.** The outer version at L4182 should follow the EXACT same pattern:
1. `lean_goal` at L4182
2. Case split on the Core step (sc → sc'): most cases preserve `sc.funcs` → `hfuncs_supp i fd h`
3. functionDef case: new closure's body comes from source (supported by `hsupp`)
4. Pattern: `fun i fd hfd => by cases hcstep; all_goals (try exact hfuncs_supp i fd hfd); ...`

### TASK 2: L5125 — non-consoleLog function call (FuncsCorr)
```lean
sorry -- non-consoleLog function call: needs sf.funcs[idx] ↔ sc.funcs[idx] correspondence
```
1. `lean_goal` at L5125
2. Needs: flat and core funcs arrays are element-wise corresponding
3. Check if CC_SimRel has a FuncsCorr field or if you need to add one

### TASK 3: L7221 — functionDef case
```lean
| functionDef fname params body isAsync isGen => sorry
```
1. `lean_goal` at L7221
2. functionDef pushes new closure to s.funcs — show Flat closureConvert matches

## ARCHITECTURALLY BLOCKED (DO NOT TOUCH)
- L4209: captured variable (multi-step)
- L4538/4561: CCStateAgree if-branches
- L5333/5341: semantic mismatch (Core allocates vs Flat steps)
- L5979: UNPROVABLE getIndex string
- L7378/7379: tryCatch CCStateAgree
- L7451: tryCatch inner
- L7559: while_ CCState threading

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
