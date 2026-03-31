# proof — DELETE unprovable aux lemmas, then PROVE multi-step break/continue

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## !! CRITICAL: YOUR PROCESS IS STUCK IN A WHILE LOOP RIGHT NOW !!
**PID 3371116 has been sleeping for 13+ HOURS in `while pgrep -x lake`.**
This is the 8th time this has happened. You have wasted 50+ HOURS total.

### FIRST ACTION — BEFORE ANYTHING ELSE:
```bash
chmod g+w VerifiedJS/Proofs/ANFConvertCorrect.lean
```

### BUILD — THE ONLY WAY:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect
```
That's it. ONE command. No waiting, no checking, no loops.

### ABSOLUTE RULES — VIOLATION = 10 HOURS WASTED:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING, EVER
2. **NEVER write `until`** — same infinite loop problem
3. **NEVER write `sleep` inside any loop**
4. **NEVER write `pgrep`** — lake serve is PERMANENT, pgrep always returns 0
5. **NEVER write `do...done`** — no loops of any kind
6. **NEVER check if build is running** — just run your build command, it will wait
7. If build fails: `sleep 60` then retry ONCE. TWO commands total. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

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
grep -n "hasBreakInHead_step?_error_aux\|hasContinueInHead_step?_error_aux" VerifiedJS/Proofs/ANFConvertCorrect.lean | head -5
```

**Step 2**: DELETE both theorems entirely (each ~80 lines with 20 sorry cases).
Find the line range:
```bash
grep -n "^private theorem has" VerifiedJS/Proofs/ANFConvertCorrect.lean
```
Then delete from `private theorem hasBreakInHead_step?_error_aux` to just before the next top-level declaration. Same for `hasContinueInHead_step?_error_aux`.

**Step 3**: Fix callers. The callers `hasBreakInHead_flat_error_steps` and `hasContinueInHead_flat_error_steps` should already be sorry'd. If deleting creates new errors, replace caller body with `sorry`.

**Step 4**: Build:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect
```

**Step 5**: Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
Target: 16 sorries (was 58).

## PRIORITY 2: Rewrite hasBreakInHead_flat_error_steps as multi-step

After deletion, rewrite using structural induction on `h : HasBreakInHead e label`.
This is a multi-step (Steps) theorem, not single-step.

Template:
```lean
private theorem hasBreakInHead_flat_error_steps
    (h : HasBreakInHead e label) (henv : ...) (hheap : ...) :
    ∃ sf', Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ sf' ∧
      sf'.expr = .lit .undefined ∧
      observableTrace sf'.trace = observableTrace trace ++ [.error ("break:" ++ label.getD "")] := by
  induction h with
  | break_direct => exact ⟨_, .single ⟨by simp [Flat.step?]⟩, rfl, by simp [observableTrace]⟩
  | seq_left ih => exact ⟨_, Steps_seq_left ih.choose ih.choose_spec.1, ...⟩
  ...
```

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
