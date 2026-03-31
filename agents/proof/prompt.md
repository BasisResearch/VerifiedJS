# proof — DELETE unprovable aux lemmas, then PROVE multi-step break/continue

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! CRITICAL: YOU HAVE BEEN STUCK FOR 10+ HOURS !!
Your LAST TWO sessions got PERMANENTLY STUCK in `while` loops.
The pattern `while pgrep -x lake > /dev/null; do sleep 5; done` is an INFINITE LOOP
because `lake serve` processes are permanent LSP servers that never exit.

### ABSOLUTE RULES — VIOLATION = WASTED SESSION:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for anything
2. **NEVER write `until`** — same problem
3. **NEVER write `sleep` inside any loop** — you will get stuck forever
4. `lake serve` is PERMANENT. `pgrep -x lake` will ALWAYS return 0.
5. To build: just run `lake build VerifiedJS.Proofs.ANFConvertCorrect` directly
6. If it fails because another build runs: wait 60 seconds with ONE `sleep 60`, then retry ONCE
7. If it fails again: skip the build and work on something else

## MEMORY: 7.7GB total, NO swap.

## STATE (03:05): 58 sorries, build PASSES

### Sorry breakdown (58 total, only 16 real):
- **40 hasBreak/hasContinue aux** (L3954-4030 + L4085-4161): FUNDAMENTALLY UNPROVABLE as stated
- **7 depth-induction** (L3825-3923): normalizeExpr_labeled_step_sim
- **2 makeEnv/objectLit/arrayLit** (L4036, L4167): inside aux lemmas (will be deleted with aux)
- **1 compound flat_arg** (L4336)
- **1 HasThrowInHead non-direct** (L4339)
- **7 expression-case** (L4370-4509): throw/return/await/yield/let/seq/if+tryCatch

## PRIORITY 1: DELETE the 42 unprovable aux sorries (58 → 16)

The `hasBreakInHead_step?_error_aux` and `hasContinueInHead_step?_error_aux` theorems
are FUNDAMENTALLY UNPROVABLE — they claim single-step (`Flat.step?`) directly produces
the break/continue error, but `step?` wraps results in the parent context.

### EXACT STEPS:

**Step 1**: Find and DELETE `hasBreakInHead_step?_error_aux` entirely.
Use `grep -n "hasBreakInHead_step?_error_aux" VerifiedJS/Proofs/ANFConvertCorrect.lean`
to find the bounds. Delete the entire theorem (it's ~80 lines with all 20 sorry cases).

**Step 2**: Find and DELETE `hasContinueInHead_step?_error_aux` entirely (symmetric, ~80 lines).

**Step 3**: Also delete the 2 makeEnv/objectLit/arrayLit sorry helpers inside those theorems.

**Step 4**: Fix any callers. The callers are `hasBreakInHead_flat_error_steps` and
`hasContinueInHead_flat_error_steps`. These should ALREADY be sorry'd — just leave them as sorry.
If deleting the aux theorems creates new errors in the callers, comment out the broken caller
body and replace with `sorry`.

**Step 5**: Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

**Step 6**: Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
Target: 16 sorries (was 58).

## PRIORITY 2: Rewrite hasBreakInHead_flat_error_steps as multi-step

After deletion, rewrite `hasBreakInHead_flat_error_steps` using structural induction on
`h : HasBreakInHead e label`. This is a multi-step (Steps) theorem, not single-step.

First check what context-lifting lemmas exist:
```
grep -n "Steps_seq\|Steps_ctx\|Steps_let\|Steps_if" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

If none exist, you'll need to write them. Each says:
"If `Flat.Steps {s | expr := e} evs {s' | expr := e'}`, then
 `Flat.Steps {s | expr := .seq e b} evs {s' | expr := .seq e' b}`"

**DO NOT attempt the multi-step rewrite BEFORE completing the deletion in Priority 1.**
Deletion is mechanical and safe. Rewriting requires LSP and careful reasoning.

## PRIORITY 3: Close expression-case sorries (if time)

After restructuring, at ~L4370-4509 (line numbers will shift):
- throw, return, await, yield, let, seq, if+tryCatch

For each: `lean_goal` → `lean_multi_attempt` with:
```
["simp_all", "exact ⟨_, _, rfl, rfl⟩", "constructor <;> simp_all", "aesop"]
```

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec own this
- Flat/Semantics.lean — jsspec modified this

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
