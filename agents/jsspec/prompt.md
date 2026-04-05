# jsspec — Close L4182 (FuncsSupported) THEN L4209 (captured var) and L5125 (FuncsCorr)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.5GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: CC now 13 sorries. Sorry count went UP +1 — FIX IT.

## CC 13 sorries remaining (UPDATED LINE NUMBERS):
- **L4182**: FuncsSupported preservation (NEW — you introduced this, close it!)
- L4209: captured variable (architecturally blocked — multi-step)
- L4538, L4561: if CCStateAgree (architecturally blocked)
- **L5125**: non-consoleLog function call (FuncsCorr needed)
- L5333, L5341: semantic mismatch call (architecturally blocked)
- L5979: getIndex string (UNPROVABLE)
- **L7221**: functionDef
- L7378, L7379: tryCatch CCStateAgree (architecturally blocked)
- L7451: tryCatch inner
- L7559: while_ CCState threading (architecturally blocked)

### TASK 1: L4182 — FuncsSupported preservation (PRIORITY 1 — YOU CREATED THIS SORRY)
```lean
have hfuncs_supp' : ∀ i (fd : Core.FuncClosure), sc'.funcs[i]? = some fd → fd.body.supported = true :=
    sorry -- FuncsSupported preservation: step? either preserves funcs or pushes supported body
```
This is at L4181-4182 in the outer wrapper of closureConvert_step_simulation.

**Strategy**:
1. `lean_goal` at L4182
2. You need: after Core takes a step (sc → sc'), all function closures in sc' have supported bodies
3. Most Core.step? cases DON'T change funcs (they're preserved from sc). For those: `exact hfuncs_supp i fd h`
4. The only case that adds to funcs is functionDef — and it pushes a body that came from the source, which is supported by `hsupp`
5. Pattern: case split on the Core step, show funcs either unchanged or extended with supported body
6. You already proved the INNER FuncsSupported invariant at L3970 — this outer one should follow the SAME pattern

**Concrete Lean sketch**:
```lean
fun i fd hfd => by
  -- sc' came from Core.step? sc, so sc'.funcs is either sc.funcs or sc.funcs ++ [new_fd]
  -- In all non-functionDef cases: sc'.funcs = sc.funcs, so hfuncs_supp i fd hfd
  -- In functionDef case: the new fd has body from source which is supported
  obtain ⟨hcstep_inner⟩ := hcstep
  sorry -- case split on hcstep_inner to show funcs preservation
```

### TASK 2: L5125 — non-consoleLog function call (FuncsCorr)
```lean
sorry -- non-consoleLog function call: needs sf.funcs[idx] ↔ sc.funcs[idx] correspondence
```
**Strategy**:
1. `lean_goal` at L5125
2. Need: if `sf.funcs[idx]? = some fd_flat` then `sc.funcs[idx]? = some fd_core` with body correspondence
3. Check if CC_SimRel already has a FuncsCorr component
4. The FuncsSupported invariant pattern (from L3464) is a good model

### TASK 3: L7221 — functionDef case
```lean
| functionDef fname params body isAsync isGen => sorry
```
1. `lean_goal` at L7221
2. functionDef adds a new closure to s.funcs
3. Need to show Flat closureConvert of functionDef matches Core functionDef step

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
