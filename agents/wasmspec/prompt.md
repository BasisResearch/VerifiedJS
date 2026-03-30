# wasmspec — Close non-blocked CC sorries. Focus on value sub-cases + functionDef.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell)
- **NEVER** use a `while` loop waiting for processes. Single `pgrep -x lake` check then proceed.
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## CONTEXT: Fix D has been REVERTED

jsspec reverted Fix D from Flat/Semantics.lean and CC. The 47 "Fix D reverted" sorry
theorems are dead code and will be deleted by jsspec. The hnoerr guards are gone.

## DO NOT TOUCH THESE:
- ANFConvertCorrect.lean — proof agent owns this
- Flat/Semantics.lean — jsspec just modified this
- forIn/forOf sorries (L1369-1370) — unprovable stubs
- "Fix D reverted" sorries — jsspec is deleting these
- ExprAddrWF sorries (L4902, L5000) — jsspec is working on these
- CCState threading (L3279, L3301, L4949, L5251) — jsspec is working on these

## YOUR TASK: Close value sub-cases + larger theorems. Target: ≥2.

### TARGET 1: value sub-cases (L3795, L4536, L4858, L4956) — MOST PROMISING

These all involve the case where all sub-expressions have already been evaluated to values.

L3795: `| some cv => sorry -- callee is value: arg stepping or call execution`
L4536: `| some cv => sorry -- value sub-case (heap reasoning needed)`
L4858: `sorry -- all props are values: heap allocation`
L4956: `sorry -- all elements are values: heap allocation`

APPROACH:
1. `lean_goal` at each line to see the full proof state
2. When all expressions are values, Core.step? and Flat.step? should take a single matching step
3. Use `lean_local_search "value"` and `lean_local_search "allValues"` to find helpers
4. Try `lean_multi_attempt` with: `["simp_all", "exact ⟨_, rfl, rfl⟩", "constructor <;> simp_all"]`

### TARGET 2: functionDef (L5130)

`| functionDef fname params body isAsync isGen => sorry`

1. `lean_goal` at L5130
2. functionDef creates a closure: Core binds fname to a closure value
3. Flat's convertExpr on functionDef should produce equivalent binding
4. Use `lean_local_search "functionDef"` to find step lemmas

### TARGET 3: newObj (L3796)

`| newObj f args => sorry`

Similar to call case. Constructor invocation.

### TARGET 4: tryCatch (L5220)

`| tryCatch body catchParam catchBody finally_ => sorry`

Sets up exception handler. Both Core and Flat enter the try body.

## WORKFLOW:
1. `lean_goal` at the sorry line — read the FULL goal
2. `lean_multi_attempt` with 6-8 tactics
3. If nothing closes it in 10 minutes, MOVE TO THE NEXT ONE
4. Log what you tried and why it failed

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean`
3. Log to agents/wasmspec/log.md
