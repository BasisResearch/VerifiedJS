# jsspec — P1: CCStateAgreeWeak REFACTOR

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 15 sorries. Your hne restructuring (P0) is done — 3 error-case sorries replaced 3 hne sorries.
- Error-case sorries (L5146, L5277, L5551) are BLOCKED until proof agent extends error propagation. Don't touch them.
- BUILD PASSES. You can use LSP for verification.

## P1: CCStateAgreeWeak — YOUR MAIN TASK

4 sorries are blocked by CCStateAgree needing to be weakened to CCStateAgreeWeak:
- **L5358** — if/else: st' includes else_ conversion state
- **L5384** — if/else: same issue, other branch
- **L8327** — tryCatch: Need CCStateAgree st st_a
- **L8443** — while_: .if cond (.seq body (.while_ cond body)) (.lit .undefined)

### What needs to happen:
1. Define `CCStateAgreeWeak` as `st_flat.counter ≥ st_core.counter` (or `≤` depending on direction) instead of `=`
2. Change the `suffices` invariant at ~L4892 from `CCStateAgree` to `CCStateAgreeWeak`
3. Update `convertExpr_state_determined` and all ~47 occurrences that produce/consume CCStateAgree
4. Re-prove or sorry the cases

### Assessment first:
Before making changes, assess:
1. Read the `CCStateAgree` definition
2. Read L4892 `suffices` block
3. Count how many cases currently prove `CCStateAgree` — are they trivially adaptable to `≤`?
4. If most cases are `rfl`-based, weakening to `≤` should be straightforward (rfl → le_refl)
5. If the refactor is too large (would break more than it fixes), document why and move to P2

### If feasible:
Make the change and fix the 4 sorry sites. Even if some intermediate cases need sorry during refactor, net -4 is worth it.

### If not feasible:
Move to P2 and work on closable sorries.

## P2: OTHER CLOSABLE SORRIES (only if P1 blocked)

Look at L8250 (tryCatch body-value without finally). This has a small sorry inside a mostly-complete proof. Read the context and see if it's closable.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgreeWeak assessment" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
