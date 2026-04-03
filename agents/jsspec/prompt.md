# jsspec — Close functionDef (L6177), then arrayLit all-values (L6043)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 14 actual sorries.

## ⚠️ YOU WASTED YOUR LAST 3+ RUNS ON BLOCKED TARGETS ⚠️
STOP investigating blocked targets. Here is your BLOCKLIST — DO NOT TOUCH:
- tryCatch (L6332, L6403) — BLOCKED by CCStateAgree
- call (L4230) — BLOCKED (no FuncsCorr)
- if-then/false (L3648, L3671) — BLOCKED by CCStateAgree
- while_ (L6510) — BLOCKED by CCStateAgree
- getIndex string (L5018) — semantic mismatch, SKIP
- forIn/forOf (L1507/L1508) — UNPROVABLE stubs

## TARGET 1: functionDef (LINE 6177)

```lean
| functionDef fname params body isAsync isGen => sorry
```

This is a LEAF case. No sub-expression stepping. No CCStateAgree issue.

### How to prove it:
1. `lean_goal` at line 6177, column 50
2. Core.step? on functionDef creates a closure value
3. Flat.convertExpr of functionDef produces some expression — check with lean_hover_info
4. Show both sides produce corresponding results
5. Use `lean_multi_attempt` to try tactics

## TARGET 2 (BACKUP): arrayLit all-values (LINE 6043)

wasmspec agent is dead (crashing for 2+ days). Take over this target.

```lean
| none =>
  sorry -- all elements are values: heap allocation (same class as other value sub-cases)
```

Context: Inside `arrayLit elems`. `Core.firstNonValueExpr elems = none` means ALL elements are values.

### How to prove it:
1. `lean_goal` at line 6043
2. Both sides allocate an array on the heap
3. Look at nearby PROVED objectLit sub-step (lines 5946-6036) for the pattern
4. Key: show `Flat.firstNonValueExpr (convertExprList elems ...) = none`
5. Search: `lean_local_search "firstNonValueExpr"`, `lean_local_search "convertExprList"`

## TARGET 3 (IF TIME): newObj (LINE 4428)

```lean
| newObj f args => sorry
```

Another leaf case. Check how Core.step? handles newObj and how Flat.convertExpr converts it.

## TARGET 4 (IF TIME): captured variable (LINE 3320)

```lean
| some idx =>
  -- Captured variable: convertExpr gives .getEnv (.var envVar) idx
  sorry
```

## COLLISION AVOIDANCE
wasmspec is DEAD. You now own the FULL file. But still be careful about concurrent edits.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target sorry
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
