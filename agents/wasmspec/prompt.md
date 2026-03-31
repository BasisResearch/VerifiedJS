# wasmspec — Help with ANF sorries after proof opens the file

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**You have wasted 80+ HOURS total in while loops. DO NOT LOOP.**

### BUILD — THE ONLY WAY:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect
```
That's it. ONE command. No waiting, no checking, no loops.

### ABSOLUTE RULES — VIOLATION = ANOTHER WASTED SESSION:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING
2. **NEVER write `until`** — same problem
3. **NEVER write `sleep` inside any loop**
4. **NEVER write `pgrep`** — lake serve is PERMANENT, pgrep always matches itself
5. **NEVER write `do...done`** — no loops of any kind
6. **NEVER check if build is running** — just run your build command
7. If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## SITUATION (14:05)
- ANF: 58 sorries. File owned by `proof` user, group read-only (`rw-r-----`).
- CC: 18 sorries — ALL BLOCKED (CCStateAgree, HeapInj, FuncsCorr issues). DO NOT TOUCH CC.
- proof agent restarts at 14:30. It will `chmod g+w` the ANF file and delete 42 aux lemmas.
- After proof finishes, ANF should have ~16-18 sorries and be group-writable.

## YOUR PLAN

### Step 1: Wait for ANF file to become writable (~15 minutes)
```bash
# Check once:
test -w VerifiedJS/Proofs/ANFConvertCorrect.lean && echo "WRITABLE" || echo "NOT YET"
```
If not writable, `sleep 300` then check ONCE more. If still not writable after that, `sleep 300` and check ONE final time. 3 checks maximum. NO LOOPS.

### Step 2: Once writable, count sorries and read the file
```bash
grep -n sorry VerifiedJS/Proofs/ANFConvertCorrect.lean
```

### Step 3: Work on the expression-case sorries

After proof deletes aux lemmas, ~16 sorries remain. The EASIEST are the expression-case sorries:

**Target sorries** (current line numbers — will shift after deletion):
- L3825: nested return-some (needs depth induction)
- L3829: nested yield-some (needs depth induction)
- L3840: compound/bindComplex cases
- L3891, L3895, L3906: same patterns
- L3923: compound/bindComplex/throw/await

**Approach for each**:
1. Use `lean_goal` to get the goal state
2. These are in `normalizeExpr_step_sim` — check what constructor case you're in
3. Try `lean_multi_attempt` with:
   ```
   ["simp_all", "exact ih_depth _ (by omega) _ _ _ _ _ _ rfl rfl rfl ⟨_, rfl⟩", "constructor <;> simp_all", "aesop"]
   ```
4. The key insight: these need `ih_depth` (the strong recursion IH) at a smaller depth

### Step 4: Work on depth-induction sorries (L4336+)

These are in `normalizeExpr_labeled_step_sim`. Similar approach — use `lean_goal` and `lean_multi_attempt`.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — ALL sorries are architecturally blocked
- Any file you don't have write permission for

## CRITICAL: LOG YOUR WORK
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
