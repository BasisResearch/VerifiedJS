# proof — DELETE unprovable aux lemmas, then PROVE multi-step break/continue

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## !! CRITICAL: YOUR PROCESS HAS BEEN STUCK IN A WHILE LOOP FOR 17+ HOURS !!
**You have wasted 80+ HOURS total in while loops. DO NOT LOOP.**

### FIRST ACTION — BEFORE ANYTHING ELSE:
```bash
chmod g+w VerifiedJS/Proofs/ANFConvertCorrect.lean
```

### BUILD — THE ONLY WAY:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect
```
That's it. ONE command. No waiting, no checking, no loops.

### ABSOLUTE RULES — VIOLATION = 10+ HOURS WASTED:
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
- **42 hasBreak/hasContinue aux** (lines 3927-4167) — FUNDAMENTALLY UNPROVABLE as single-step claims
- **7 depth-induction** (normalizeExpr_labeled_step_sim)
- **1 compound flat_arg** (L3840)
- **1 HasThrowInHead non-direct** (L3923)
- **7 expression-case** (return-some L3825, yield-some L3829, L3891, L3895, L3906, L3923, and throw/await/yield/let/seq/if+tryCatch)

## PRIORITY 1: DELETE the 42 unprovable aux sorries (58 → 18)

The `hasBreakInHead_step?_error_aux` and `hasContinueInHead_step?_error_aux` theorems are FUNDAMENTALLY UNPROVABLE — they claim single-step produces break/continue error, but step? wraps results in the parent context.

### EXACT STEPS:

**Step 1**: Find the aux lemmas:
```bash
grep -n "hasBreakInHead_step?_error_aux\|hasContinueInHead_step?_error_aux" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

**Step 2**: Delete `hasBreakInHead_step?_error_aux` — everything from the `private theorem hasBreakInHead_step?_error_aux` line through the `| makeEnv_values _ | objectLit_props _ | arrayLit_elems _ => sorry` line. Keep the `hasBreakInHead_flat_error_steps` theorem but replace its proof body with `sorry`.

**Step 3**: Delete `hasContinueInHead_step?_error_aux` — same structure. Keep `hasContinueInHead_flat_error_steps` but replace proof body with `sorry`.

**Step 4**: The `_flat_error_steps` theorems should now look like:
```lean
private theorem hasBreakInHead_flat_error_steps
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label)
    (sf : Flat.State) (hsf : sf.expr = e)
    (hewf : ExprWellFormed e sf.env) :
    ∃ (sf' : Flat.State) (evs : List Core.TraceEvent),
      Flat.Steps sf evs sf' ∧
      sf'.expr = .lit .undefined ∧
      sf'.env = sf.env ∧ sf'.heap = sf.heap ∧
      sf'.funcs = sf.funcs ∧ sf'.callStack = sf.callStack ∧
      sf'.trace = sf.trace ++ evs ∧
      observableTrace evs = observableTrace [.error ("break:" ++ label.getD "")] := by
  sorry -- TODO: multi-step induction on HasBreakInHead
```
(Same for hasContinueInHead_flat_error_steps)

**Step 5**: Build and count:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect && grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean
```
Expected: 58 - 42 + 2 = 18 sorries

## PRIORITY 2: Rewrite _flat_error_steps as multi-step (18 → 16)

After deletion, rewrite using structural induction on `h : HasBreakInHead e label`:
```lean
private theorem hasBreakInHead_flat_error_steps ... := by
  induction h with
  | break_direct =>
    exact ⟨_, [_], .tail ⟨by cases sf; simp_all [Flat.step?]⟩ (.refl _), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | seq_left ih =>
    -- Get sub-steps from IH, then wrap in seq context
    sorry -- use Steps_seq_left or similar context-lifting lemma
  | ...
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
