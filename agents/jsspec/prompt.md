# jsspec — Close L4188 (FuncsSupported) THEN L5131, L7227

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## STATUS: CC has 13 sorries. You've been running 11+ runs with 0 CC sorry closures.

**THIS IS NOT ACCEPTABLE.** Close L4188 this run or explain EXACTLY what blocks you.

## CC 13 sorries (CURRENT LINE NUMBERS — VERIFIED 13:05):
- **L4188**: FuncsSupported preservation ← CLOSE THIS NOW
- L4215: captured variable (architecturally blocked)
- L4544, L4567: if CCStateAgree (architecturally blocked)
- **L5131**: non-consoleLog function call (FuncsCorr needed)
- L5339, L5347: semantic mismatch call (architecturally blocked)
- L5985: getIndex string (UNPROVABLE)
- **L7227**: functionDef
- L7384: tryCatch body-value (blocked)
- L7385: tryCatch with finally (blocked)
- L7457: tryCatch inner
- L7565: while_ CCState threading (blocked)

### TASK 1: L4188 — FuncsSupported preservation (DO THIS FIRST)
```lean
have hfuncs_supp' : ∀ i (fd : Core.FuncClosure), sc'.funcs[i]? = some fd → fd.body.supported = true :=
    sorry -- FuncsSupported preservation: step? either preserves funcs or pushes supported body
```

**Strategy**: Case split on the Core step. Most cases preserve `sc.funcs` so `hfuncs_supp i fd h` closes immediately. The `functionDef` case adds a new closure whose body comes from source (supported by `hsupp`).

1. `lean_goal` at L4188 to see exact context
2. Try: `fun i fd hfd => by cases hcstep <;> (try exact hfuncs_supp i fd hfd) <;> sorry`
3. For the functionDef case: the new closure body is the function body from source, which is supported. Check `Array.push` indexing — `Array.getElem?_push` should help.

### TASK 2: L5131 — non-consoleLog function call
Once L4188 is done, this needs flat funcs ↔ core funcs correspondence.

### TASK 3: L7227 — functionDef case
Both sides push new closure to funcs. Should follow from closureConvert on body.

## PRIORITY: L4188 ONLY until it's closed. Nothing else matters.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
