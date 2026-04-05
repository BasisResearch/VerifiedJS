# jsspec — Close L3970 (FuncsSupported) — you're SO CLOSE

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~485MB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION
proof and wasmspec build ANFConvertCorrect. Before you build CC, check:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 1, wait 60s then check again. Only ONE build at a time or everything OOMs.

## GREAT PROGRESS LAST RUN — Call case expanded, only L3970 remains

You expanded the call case from 1 broad sorry to 1 targeted sorry. All non-closure subcases proved. 5 forward lemmas added to Core/Semantics.lean. Excellent work.

## CC has 13 sorries. Current targets:

### TASK 1: L3970 — closure.body.supported (PRIORITY 1 — CLOSE IT)
The only remaining sorry in the call case of Core_step_preserves_supported.

**What you need**: `closure.body.supported = true` where `closure = s.funcs[idx]`.

**Approach (try in order)**:
1. `lean_goal` at L3970 to see exact state
2. **Option A (preferred)**: Add `(hfuncs_supp : ∀ i fd, s.funcs[i]? = some fd → fd.body.supported = true)` parameter to `Core_step_preserves_supported`
3. At L3970: `exact hfuncs_supp idx closure hfunc` (adjust names to match goal)
4. At the call site (~L4175 in closureConvert_step_simulation), prove the invariant holds:
   - Initial program: all funcs supported (from program.supported)
   - After functionDef step: new func has supported body (from the expr being supported)
   - After all other steps: funcs unchanged → invariant preserved
5. **Option B**: Check if there's already enough in scope — `lean_hover_info` on hypotheses at L3970

### TASK 2: L5116 — non-consoleLog function call (only if Task 1 done)
Uses similar FuncsCorr invariant between `sf.funcs` and `sc.funcs`.

### TASK 3: L7212 — functionDef case (only if Tasks 1-2 done)

## ARCHITECTURALLY BLOCKED (DO NOT TOUCH)
- L4529/4552: CCStateAgree if-branches
- L5324/5332: semantic mismatch (Core allocates vs Flat steps)
- L5970: UNPROVABLE getIndex string
- L7369/7370: tryCatch CCStateAgree
- L7442: tryCatch inner
- L7550: while_ CCState threading

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
