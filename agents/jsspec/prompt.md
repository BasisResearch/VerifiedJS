# jsspec — Close L4185 (FuncsSupported) THEN L5128, L7224

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.4GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: CC has 13 sorries. You've been running for 10 runs with 0 CC sorry closures.

**THIS IS NOT ACCEPTABLE.** You have done great infrastructure work (forward lemmas, call case expansion) but you need to CLOSE SORRIES. Focus ONLY on L4185 — it is the most tractable.

## CC 13 sorries (CURRENT LINE NUMBERS):
- **L4185**: FuncsSupported preservation ← CLOSE THIS NOW
- L4212: captured variable (architecturally blocked)
- L4541, L4564: if CCStateAgree (architecturally blocked)
- **L5128**: non-consoleLog function call (FuncsCorr needed)
- L5336, L5344: semantic mismatch call (architecturally blocked)
- L5982: getIndex string (UNPROVABLE)
- **L7224**: functionDef
- L7382: tryCatch body-value with finally (blocked)
- L7454: tryCatch inner
- L7562: while_ CCState threading (blocked)

### TASK 1: L4185 — FuncsSupported preservation (YOU CREATED THIS — CLOSE IT)
```lean
have hfuncs_supp' : ∀ i (fd : Core.FuncClosure), sc'.funcs[i]? = some fd → fd.body.supported = true :=
    sorry -- FuncsSupported preservation: step? either preserves funcs or pushes supported body
```

**Strategy**: Case split on the Core step. Most cases preserve `sc.funcs` so `hfuncs_supp i fd h` closes immediately. The `functionDef` case adds a new closure whose body comes from source (supported by `hsupp`).

1. `lean_goal` at L4185
2. Try: `fun i fd hfd => by cases hcstep <;> (try exact hfuncs_supp i fd hfd) <;> sorry`
3. For the functionDef case: the new closure body is the function body from source, which is supported

### TASK 2: L5128 — non-consoleLog function call
Once L4185 is done, this needs FuncsCorr (flat funcs ↔ core funcs correspondence). Check CC_SimRel.

### TASK 3: L7224 — functionDef case
Both sides push new closure to funcs. Should follow from closureConvert on body.

## PRIORITY: L4185 ONLY until it's closed. Nothing else matters.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
