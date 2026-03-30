# wasmspec — Close non-blocked CC sorries. Focus on newObj + functionDef + tryCatch.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell)
- **NEVER** use a `while` loop waiting for processes. Single `pgrep -x lake` check then proceed.
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## DO NOT TOUCH THESE SORRIES:
- 47 "Fix D reverted" sorries (lines 1627-2606) — BLOCKED
- 2 forIn/forOf sorries (L1369-1370) — unprovable stubs
- ANFConvertCorrect.lean — proof agent owns this
- L4890, L4988 (ExprAddrWF) — jsspec is working on these
- L3267, L4937 (CCState threading) — jsspec is working on these

## YOUR TASK: Close non-blocked CC sorries. Target: ≥2.

### TARGET 1: newObj (L3784) — HIGHEST PRIORITY

`| newObj f args => sorry`

1. `lean_goal` at L3784 to see the full proof state
2. newObj is similar to call — evaluate f and args, create new object
3. Core.step? and Flat.step? should have matching newObj rules
4. Use `lean_local_search "newObj"` to find relevant lemmas
5. Try `lean_multi_attempt` at L3784 with simple tactics

### TARGET 2: functionDef (L5118)

`| functionDef fname params body isAsync isGen => sorry`

1. `lean_goal` at L5118
2. Core.step? on functionDef creates a closure and binds it to fname
3. Flat.step? on converted expression should do the same
4. CC_SimRel must hold: converted closure body relates to original

### TARGET 3: tryCatch (L5208)

`| tryCatch body catchParam catchBody finally_ => sorry`

1. `lean_goal` at L5208
2. tryCatch sets up a handler — both Core and Flat enter the try body
3. CC_SimRel for the body should follow from the conversion

### TARGET 4: getIndex string mismatch (L4352)

`sorry -- getIndex string both-values: Flat/Core semantic mismatch`

1. `lean_goal` at L4352 — this may be a genuine semantic mismatch
2. If unprovable, document WHY and move on

### TARGET 5: convertExpr_not_lit (L2754, L2864)

These need `convertExpr_not_lit` for stub constructors.

1. `lean_local_search "convertExpr_not_lit"` to find if it exists
2. If not, check `.lake/_tmp_fix/` for staged proofs
3. Write a simple lemma: `convertExpr ≠ .lit _` for the relevant constructors

## WORKFLOW FOR EACH SORRY:
1. `lean_goal` at the sorry line — read the FULL goal
2. `lean_multi_attempt` with 6-8 tactics
3. If nothing closes it in 10 minutes, MOVE TO THE NEXT ONE
4. Log what you tried and why it failed

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean`
3. Log to agents/wasmspec/log.md

## TARGET: Close at least 2 non-blocked sorries → CC grep count down from 69
