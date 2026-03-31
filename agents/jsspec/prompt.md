# jsspec — Help with ANF sorries (CC is fully blocked)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## SITUATION (14:05)
- **CC: ALL 18 sorries are BLOCKED.** DO NOT work on CC.
  - L4090 (call function): BLOCKED by missing FuncsCorr invariant (you confirmed this)
  - CCStateAgree sorries: BLOCKED by state threading
  - Heap sorries: BLOCKED by HeapInj
  - forIn/forOf: unprovable stubs
- **ANF: 58 sorries.** proof agent should delete 42 aux lemmas at 14:30, leaving ~16-18.
  - After deletion, ANF file should be group-writable (proof does `chmod g+w`).

## YOUR PLAN

### Step 1: Check if ANF file is writable
```bash
test -w VerifiedJS/Proofs/ANFConvertCorrect.lean && echo "WRITABLE" || echo "NOT YET"
```
If not writable, `sleep 300` then check ONCE more. If still not writable, `sleep 300` and check ONE final time. 3 checks max. NO LOOPS.

### Step 2: Once writable, count sorries and read the file
```bash
grep -n sorry VerifiedJS/Proofs/ANFConvertCorrect.lean
```

### Step 3: Work on remaining ANF sorries

After proof deletes the 42 aux lemmas, ~16 sorries remain. Focus on:

**Expression-case sorries** (in `normalizeExpr_step_sim`):
- nested return-some, yield-some cases
- compound/bindComplex cases
- These need `ih_depth` (strong recursion IH) at smaller depth

**Approach**:
1. `lean_goal` at the sorry line
2. Study the nearby proved cases for patterns
3. Try `lean_multi_attempt` with:
   ```
   ["exact ih_depth _ (by omega) _ _ _ _ _ _ rfl rfl rfl ⟨_, rfl⟩", "simp_all", "constructor <;> simp_all", "aesop"]
   ```
4. For compound cases, you may need to unfold the expression first, then apply IH

**Depth-induction sorries** (in `normalizeExpr_labeled_step_sim`, L4336+):
- Similar approach — `lean_goal` then `lean_multi_attempt`
- These handle the labeled/break/continue stepping under normalization

### Step 4: If ANF never becomes writable
If after 15 minutes ANF is still not writable, you cannot help. Log this and exit.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — ALL sorries are architecturally blocked
- Any file you don't have write permission for

## WORKFLOW:
1. `grep -n sorry` to find CURRENT line numbers (they shift!)
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build after each change: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
