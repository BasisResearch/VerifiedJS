# proof — UNCOMMENT hasAbruptCompletion + NoNestedAbrupt proofs, close remaining cases

## RULES
- Edit: ANFConvertCorrect.lean AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build EndToEnd: `lake build VerifiedJS.Proofs.EndToEnd`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2.9GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: ANF down to 25 real sorries (was 27). You're making great progress!

## KEY INSIGHT: The proofs are ALREADY WRITTEN, just commented out!

hasAbruptCompletion_step_preserved (L9383) has `sorry` but the ENTIRE proof is in a block comment (L9384-9656) with 25+ cases PROVED. Only 5 cases are sorry'd inside: call (L9612), newObj (L9613), getEnv (L9614), objectLit (L9641), tryCatch (L9656).

NoNestedAbrupt_step_preserved (L9662) is the same: full proof in block comment (L9663-9969), only call (L9925), newObj (L9926), getEnv (L9927), objectLit (L9954), tryCatch (L9969) are sorry'd.

## YOUR #1 PRIORITY: Uncomment and activate the proofs

### Step 1: Fix the blocking issue
The comment says "split at hstep fails with have bindings in step? unfolding". The call/newObj/getEnv cases fail because `Flat.step?` uses `have` bindings for these constructors. Try:
```lean
| call f fenv args =>
  simp only [hasAbruptCompletion] at hac
  unfold Flat.step? at hstep
  -- If split fails, try: simp only [Flat.step?] at hstep
  -- Or: dsimp only [Flat.step?] at hstep; split at hstep
  sorry
```

### Step 2: Uncomment the proofs
1. Remove `sorry` at L9383
2. Remove `/-` at L9384 and `-/` at L9656
3. Same for L9662: remove `sorry`, remove `/-` at L9663 and `-/` at L9969
4. The uncommented proofs will have 5 sorry cases each — that's 10 targeted sorries instead of 2 monolithic ones, but represents REAL progress because 50+ cases are now proved

### Step 3: Try to close some of the 5 remaining cases
- **objectLit** (L9641, L9954): These are list-based like makeEnv/arrayLit. Try the same pattern — need `hasAbruptCompletionPropList_firstNonValue_preserved` or similar.
- **getEnv** (L9614, L9927): Two sub-expressions (envExpr, idx). Try manual case split:
```lean
| getEnv envExpr idx =>
  simp only [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
  obtain ⟨he, hi⟩ := hac
  unfold Flat.step? at hstep
  -- try dsimp or simp to unfold the have bindings
  sorry
```

### Priority 2: break/continue compound (L10360, L10413)
Only if Priority 1 is done or blocked.

## What NOT to work on:
- Group A (L7696-7882): eval context lifting — PARKED
- If compound (L9257-9331): needs trivialChain — PARKED
- Compound throw/return/await/yield (L8523-9003): wasmspec handles these

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
