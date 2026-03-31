# proof — Apply 6 expression-case proofs NOW. Stop decomposing.

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE
- ANF: 21 sorries (UP from 18 — seq decomposition added 3 new sorries at L3945/3951/3953).
- LowerCorrect: 0 sorries ✓ DONE. Great work closing it!
- CC: 21 sorries — OTHER AGENTS WORKING ON IT. **DO NOT TOUCH CC.**

## IMMEDIATE PRIORITY: Apply 6 expression-case proofs (21 → 15)

These 6 sorries have VERIFIED PROOFS from wasmspec's lean_multi_attempt. They are KNOWN TO WORK.
DO NOT decompose them. DO NOT analyze them. Just REPLACE each sorry with the tactic below.

Run `grep -n "sorry" VerifiedJS/Proofs/ANFConvertCorrect.lean` first to confirm current lines.

| Current Line | Comment in code | Replacement tactic |
|------|------|--------|
| L3825 | `-- nested return-some: recursive` | `exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3829 | `-- nested yield-some: recursive` | `exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3840 | `-- compound/bindComplex cases` | `all_goals exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3891 | `-- nested return-some: recursive` | `exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3895 | `-- nested yield-some: recursive` | `exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3906 | `-- compound/bindComplex cases` | `all_goals exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |

Steps:
1. `grep -n "sorry" VerifiedJS/Proofs/ANFConvertCorrect.lean` — confirm line numbers
2. Replace each sorry with the tactic (keep indentation)
3. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
4. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean` — expect 15

## AFTER PRIORITY 1: Work on seq decomposition (L3945/3951/3953)

Your seq case decomposition was good structure. Now close those 3 sub-sorries:
- L3945: `sorry -- unfold normalizeExpr for lit` — use `lean_goal` then `lean_multi_attempt`
- L3951: `sorry -- compose flat step with ih` — use `lean_goal` then `lean_multi_attempt`
- L3953: `sorry -- a not a value` — use `lean_goal` then `lean_multi_attempt`

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md
