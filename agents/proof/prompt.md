# proof — DELETE unprovable aux lemmas, then PROVE multi-step break/continue

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! YOU HAVE WASTED 34+ HOURS STUCK IN WHILE LOOPS !!
**YOUR LAST 5 SESSIONS DID ZERO WORK because of `while pgrep` loops.**
`lake serve` processes are PERMANENT. `pgrep -x lake` will ALWAYS return 0.

### ABSOLUTE RULES — READ THESE BEFORE DOING ANYTHING:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING, EVER
2. **NEVER write `until`** — same infinite loop problem
3. **NEVER write `sleep` inside any loop**
4. To build: just run `lake build VerifiedJS.Proofs.ANFConvertCorrect` directly
5. If build fails: ONE `sleep 60`, then retry ONCE. That's it.
6. If you find yourself writing `while` or `until`: STOP. DELETE IT. You will waste another 10+ hours.

## MEMORY: 7.7GB total, NO swap.

## FIRST ACTION: Make ANF file writable for other agents
Run: `chmod g+w VerifiedJS/Proofs/ANFConvertCorrect.lean`

## STATE: 58 sorries, build PASSES

### Sorry breakdown (58 total, only 16 real):
- **42 hasBreak/hasContinue aux + makeEnv/objectLit/arrayLit** (FUNDAMENTALLY UNPROVABLE — wrong approach)
- **7 depth-induction** (normalizeExpr_labeled_step_sim)
- **1 compound flat_arg**
- **1 HasThrowInHead non-direct**
- **7 expression-case** (throw/return/await/yield/let/seq/if+tryCatch)

## PRIORITY 1: DELETE the 42 unprovable aux sorries (58 → 16)

The `hasBreakInHead_step?_error_aux` and `hasContinueInHead_step?_error_aux` theorems
are FUNDAMENTALLY UNPROVABLE — they claim single-step produces break/continue error,
but step? wraps results in the parent context.

### EXACT STEPS:

**Step 1**: Find the theorem bounds:
```bash
grep -n "hasBreakInHead_step?_error_aux\|hasContinueInHead_step?_error_aux" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

**Step 2**: DELETE both theorems entirely (each ~80 lines with 20 sorry cases).
Use `sed` or your editor to remove everything from `private theorem hasBreakInHead_step?_error_aux`
through the end of its proof (look for the next `private theorem` or top-level declaration).
Do the same for `hasContinueInHead_step?_error_aux`.

**Step 3**: Fix callers. The callers `hasBreakInHead_flat_error_steps` and `hasContinueInHead_flat_error_steps`
should already be sorry'd. If deleting creates new errors, replace caller body with `sorry`.

**Step 4**: Build:
```bash
pkill -f "lean.*\.lean" 2>/dev/null; sleep 5
lake build VerifiedJS.Proofs.ANFConvertCorrect
```

**Step 5**: Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
Target: 16 sorries (was 58).

## PRIORITY 2: Rewrite hasBreakInHead_flat_error_steps as multi-step

After deletion, rewrite using structural induction on `h : HasBreakInHead e label`.
This is a multi-step (Steps) theorem, not single-step.

Check for context-lifting lemmas:
```bash
grep -n "Steps_seq\|Steps_ctx\|Steps_let\|Steps_if" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

## PRIORITY 3: Close expression-case sorries (if time)

For each: `lean_goal` → `lean_multi_attempt` with:
```
["simp_all", "exact ⟨_, _, rfl, rfl⟩", "constructor <;> simp_all", "aesop"]
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec own this
- Flat/Semantics.lean

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md
