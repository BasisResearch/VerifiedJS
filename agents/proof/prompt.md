# proof — DELETE unprovable ANF aux, then close expression-case sorries

## RULES
- Edit: ANFConvertCorrect.lean AND LowerCorrect.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Lower: `lake build VerifiedJS.Proofs.LowerCorrect`

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**You have wasted 100+ HOURS total in while loops. DO NOT LOOP.**

### BUILD — THE ONLY WAY:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect
lake build VerifiedJS.Proofs.LowerCorrect
```
ONE command each. No waiting, no checking, no loops.

### ABSOLUTE RULES — VIOLATION = 10+ HOURS WASTED:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING, EVER
2. **NEVER write `until`** — same infinite loop problem
3. **NEVER write `sleep` inside any loop**
4. **NEVER write `pgrep`** — lake serve is PERMANENT, pgrep always returns 0
5. **NEVER write `do...done`** — no loops of any kind
6. **NEVER check if build is running** — just run your build command, it will wait
7. If build fails: `sleep 60` then retry ONCE. TWO commands total. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE
- ANF: 58 sorries (build passes). File is now group-writable ✓
- LowerCorrect: 1 sorry (lower_sim_steps L52). Build may have errors — check.
- CC: 29 sorries — OTHER AGENTS WORKING ON IT. **DO NOT TOUCH CC.**

## PRIORITY 1: DELETE the 42 unprovable aux sorries in ANF (58 → ~18)

The `hasBreakInHead_step?_error_aux` and `hasContinueInHead_step?_error_aux` theorems are FUNDAMENTALLY UNPROVABLE — they expand one step? into a parent context, but step? doesn't do that.

### EXACT STEPS:

**Step 1**: Find the blocks:
```bash
grep -n "hasBreakInHead_step?_error_aux\|hasContinueInHead_step?_error_aux\|hasBreakInHead_flat_error_steps\|hasContinueInHead_flat_error_steps" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

**Step 2**: Delete `hasBreakInHead_step?_error_aux` — everything from `private theorem hasBreakInHead_step?_error_aux` through all its sorry cases. Keep `hasBreakInHead_flat_error_steps` but replace its proof body with `sorry`.

**Step 3**: Delete `hasContinueInHead_step?_error_aux` — same pattern. Keep `hasContinueInHead_flat_error_steps` but sorry its body.

**Step 4**: Build and count:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect && grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean
```

Expected: 58 → ~18 sorries.

## PRIORITY 2: Apply wasmspec's 7 expression-case proofs

wasmspec verified these via lean_multi_attempt. Apply them if ANF deletion succeeds:

| Line | Tactic |
|------|--------|
| L3825 (return.some.return.some) | `exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3829 (return.some.yield.some) | same as L3825 |
| L3840 (return.some compound) | `all_goals exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3891 (yield.some.return.some) | same as L3825 |
| L3895 (yield.some.yield.some) | same as L3825 |
| L3906 (yield.some compound) | same as L3840 |
| L3923 (top-level compound) | `all_goals exact ⟨[], sf, Flat.Steps.refl, ⟨k, n, m, hnorm, hk⟩, rfl, rfl, rfl, rfl, hwf⟩` |

**IMPORTANT**: Line numbers will shift after deletion. Use `grep -n` to find the current lines.

## PRIORITY 3: Close LowerCorrect sorry (L52)

`lower_sim_steps` needs induction on `ANF.Steps`. Pattern:
```lean
intro sa ir tr sa' hrel hsteps
induction hsteps with
| refl => exact ⟨ir, IR.IRSteps.refl, hrel⟩
| step t sa₁ rest sa₂ sa₃ hstep hrest ih =>
  obtain ⟨ir₂, ir_trace₂, hirsteps₂, hrel₂, hobs₂⟩ := IR.LowerSimRel.step_sim s t h sa₁ ir hrel hstep
  obtain ⟨ir₃, hirsteps₃, hrel₃⟩ := ih hrel₂
  exact ⟨ir₃, IR.IRSteps.append hirsteps₂ hirsteps₃, hrel₃⟩
```
Use `lean_goal` at L52 to see exact types, then `lean_multi_attempt`.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md
