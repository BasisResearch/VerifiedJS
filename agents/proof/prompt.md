# proof — Close tryCatch catch handlers + break/continue error propagation

## RULES
- Edit: ANFConvertCorrect.lean AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build EndToEnd: `lake build VerifiedJS.Proofs.EndToEnd`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.4GB available right now.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: AMAZING PROGRESS! ANF down to 27 sorries (was 34).

You proved makeEnv, objectLit, arrayLit in hasAbruptCompletion AND most NoNestedAbrupt cases! Excellent work.

## YOUR TARGETS NOW:

### Priority 1: tryCatch catch handler sorries (2 sorries)
- **L9759**: hasAbruptCompletion tryCatch catch handler. When body throws error (not return:, not callFrame), the catch triggers: `sf' = {expr = seq (Let.subst param thrownVal catchBody) fin, ...}`. Need to show `hasAbruptCompletion sf'.expr = false` given `hasAbruptCompletion catchBody = false` and `hasAbruptCompletion fin = false`. Key: need `hasAbruptCompletion_subst_preserved` lemma.
- **L10190**: NoNestedAbrupt tryCatch catch handler. Same pattern but for NoNestedAbrupt. When body errors, catch fires. Need `NoNestedAbrupt_subst_preserved` or show substitution preserves NoNestedAbrupt.

### Approach for catch handlers:
The catch case unfolds to something like `seq (catchBody[param := thrownVal]) fin` (with finally) or just `catchBody[param := thrownVal]` (without finally). You need:
1. Check what `Flat.step?` produces for the catch case — use `lean_goal` at the sorry
2. If it produces `Let.subst param val catchBody`, you need a lemma: substituting a value into an expression preserves hasAbruptCompletion/NoNestedAbrupt
3. If the substitution lemma doesn't exist, create it (should be straightforward structural induction)

### Priority 2: break/continue error propagation (2 sorries)
- **L10603**: break compound cases — `HasBreakInHead` compound constructors
- **L10656**: continue compound cases — `HasContinueInHead` compound constructors

Both say "Requires Flat.step? error propagation". The issue: when break/continue appears inside a compound expression (like `seq (break l) rest`), Flat.step? should propagate the error event. The direct case (just `.break label`) is already proved.

### What NOT to work on:
- Group A (L7696-7882): eval context lifting — PARKED, needs major infrastructure
- If compound (L9257/9258/9330/9331): needs trivialChain — PARKED
- Call all-values (L9630): unknown function body — HARD, defer
- NoNestedAbrupt call all-values (L10058): same — defer

## APPROACH
1. Use `lean_goal` at L9759 to see the exact proof state for catch handler
2. Check if `hasAbruptCompletion` is preserved through `Let.subst` (grep for it)
3. If not, write the lemma and close both catch handler sorries (-2)
4. Then try break/continue compound cases (-2)
Target: -2 to -4 this run.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
