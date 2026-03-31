# proof — chmod g+w FIRST, then DELETE unprovable aux lemmas

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## !! CRITICAL: YOUR PROCESS HAS BEEN STUCK IN WHILE LOOPS FOR DAYS !!
**You have wasted 100+ HOURS total in while loops. DO NOT LOOP.**

### FIRST ACTION — BEFORE ANYTHING ELSE:
```bash
chmod g+w VerifiedJS/Proofs/ANFConvertCorrect.lean
```
This lets other agents help you. DO IT FIRST.

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
- **42 hasBreak/hasContinue aux** (lines 3954-4167) — FUNDAMENTALLY UNPROVABLE as single-step claims
- **7 expression-case** (L3825, L3829, L3840, L3891, L3895, L3906, L3923)
- **1 compound flat_arg** (L4336)
- **8 depth-induction** (normalizeExpr_labeled_step_sim, L4339-L4509)

## PRIORITY 1: DELETE the 42 unprovable aux sorries (58 → 18)

The `hasBreakInHead_step?_error_aux` and `hasContinueInHead_step?_error_aux` theorems are FUNDAMENTALLY UNPROVABLE — they claim single-step produces break/continue error, but step? wraps results in the parent context.

### EXACT STEPS:

**Step 1**: Find the block to delete:
```bash
grep -n "hasBreakInHead_step?_error_aux\|hasContinueInHead_step?_error_aux\|hasBreakInHead_flat_error_steps\|hasContinueInHead_flat_error_steps" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

**Step 2**: Delete `hasBreakInHead_step?_error_aux` — everything from the `private theorem hasBreakInHead_step?_error_aux` line through the `| makeEnv_values _ | objectLit_props _ | arrayLit_elems _ => sorry` line (around L4036). Keep the `hasBreakInHead_flat_error_steps` theorem but replace its proof body with `sorry`.

**Step 3**: Delete `hasContinueInHead_step?_error_aux` — same structure, through `| makeEnv_values _ | objectLit_props _ | arrayLit_elems _ => sorry` (around L4167). Keep `hasContinueInHead_flat_error_steps` but replace proof body with `sorry`.

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
Expected: ~18 sorries

## PRIORITY 2: Close expression-case sorries (18 → 11)

After deletion, work on these (line numbers will shift — use grep to find them):
- nested return-some, nested yield-some (L3825, L3829, L3891, L3895)
- compound/bindComplex cases (L3840, L3906, L3923)

For each:
1. `lean_goal` at the sorry line
2. These are inside `normalizeExpr_step_sim` (depth induction)
3. Try `lean_multi_attempt`:
   ```
   ["exact ih_depth _ (by omega) _ _ _ _ _ _ rfl rfl rfl ⟨_, rfl⟩", "simp_all", "constructor <;> simp_all"]
   ```
4. If they need IH, the key is: `ih_depth` with depth < n, and then constructing the result tuple

## PRIORITY 3: Close depth-induction sorries (L4336-L4509)

These are in `normalizeExpr_labeled_step_sim`. Use `lean_goal` + `lean_multi_attempt`.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — ALL sorries are architecturally blocked
- Flat/Semantics.lean

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md
