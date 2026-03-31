# wasmspec — Close CC setIndex sub-stepping sorries + help proof on ANF

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 22 grep-sorry hits, ANF 18 sorries (proof agent deleted 42 aux).

## YOUR TARGETS (in priority order)

### Target 1: setIndex value-stepping (L5212) — MEDIUM

At L5212, obj and idx are values but the `value` arg needs stepping. Pattern:
1. `lean_goal` at L5212 to see full proof state
2. Need IH on `value` (the third arg of setIndex)
3. Core steps the inner value expression; Flat does same with converted version
4. Then reconstruct setIndex with stepped value and unchanged obj/idx
5. `lean_multi_attempt` with IH-based approaches

### Target 2: setIndex idx-stepping (L5215) — MEDIUM

At L5215, obj is a value but idx needs stepping. Same pattern as above but stepping `idx`.
1. `lean_goal` at L5215
2. Need IH on `idx`
3. Core steps idx; Flat does same
4. Reconstruct setIndex with stepped idx

### Target 3: Help proof agent with ANF expression-case sorries

ANF file is NOW GROUP-WRITABLE (rw-rw----). Your 7 expression-case proofs from prior runs are ready to apply. BUT proof agent may already be applying them (check via `grep -n sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`). Only apply if proof agent hasn't gotten to them yet.

The proofs you verified:
| Current Sorry | Tactic |
|---------------|--------|
| L3825 (return.some.return.some) | `exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3829 (return.some.yield.some) | same as L3825 |
| L3840 (return.some compound) | `all_goals exact ih _ (by simp [Flat.Expr.depth] at hd ⊢; omega) _ _ _ _ _ (by intro arg n'; exact ⟨_, by simp [pure, StateT.run]⟩) hnorm _ rfl (by cases hwf; assumption)` |
| L3891 (yield.some.return.some) | same as L3825 |
| L3895 (yield.some.yield.some) | same as L3825 |
| L3906 (yield.some compound) | same as L3840 |
| L3923 (top-level compound) | `all_goals exact ⟨[], sf, Flat.Steps.refl, ⟨k, n, m, hnorm, hk⟩, rfl, rfl, rfl, rfl, hwf⟩` |

### SKIP (architecturally blocked):
- L1507-1508: forIn/forOf stubs
- L3262: captured var (HeapInj)
- L3590, L3613: CCStateAgree
- L4131, L4133: call function/non-closure (jsspec handles)
- L4302: newObj
- L4892: getIndex string
- L5547, L5643, L5650: heap allocation
- L5746-5747: arrayLit CCState + functionDef
- L5855, L5858: tryCatch (jsspec handles)
- L5890: while_ CCState

### COLLISION AVOIDANCE
jsspec works on L4100-4200 and L5800-5900. You work on L5000-5650. Do NOT edit the same regions.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
