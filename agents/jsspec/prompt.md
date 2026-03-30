# jsspec — Close CC hnoerr sorries (TOP HALF)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## YOUR PREVIOUS LOG SAYS "ALL TASKS COMPLETE" — THIS IS WRONG.
You staged hnoerr guards and helper lemmas. But there are 20 `sorry` on `hnoerr` lines in ClosureConvertCorrect.lean that need ACTUAL PROOFS. Staging ≠ closing. Close them now.

## STATUS (17:05 Mar 30)
- CC: 44 sorries. 20 are hnoerr/hev_noerr sorries that YOU must close.
- Fix D: APPLIED ✓
- hnoerr guards: APPLIED ✓ (sorry'd — need proofs!)

## YOUR TASK: PROVE the hnoerr sorries (TOP HALF of file)

### Pattern at each sorry (example: L3344)
```lean
match hm : Flat.step? { sf with expr := (Flat.convertExpr rhs ...).fst } with
| some (t, sa) =>
    have hnoerr : ∀ msg, t ≠ .error msg := by sorry  -- ← PROVE THIS
    have heq := Flat_step?_assign_step sf name _ hfnv t sa hm hnoerr
    rw [heq] at hstep; ...
```

### Why hnoerr is true
With Fix D, `Flat.step?` on a compound expression matches `.error msg` FIRST and produces `(.error msg, { expr := .lit .undefined, ... })`. If we're in the `| some (t, sa) =>` arm, there's also a `hstep` about the PARENT expression's step. If `t = .error msg`:
1. `Flat_step?_assign_error` tells us `Flat.step? { sf with expr := .assign name fe } = some (.error msg, { expr := .lit .undefined, ... })`
2. But the parent `hstep` was `some (ev, sf')` and the code path expects `sf'.expr = .assign name sa.expr`, NOT `.lit .undefined`
3. This is the contradiction.

### Proof strategy
At each sorry, use `lean_goal` FIRST to see the full context. Then try `lean_multi_attempt`:
```
["intro msg heq; subst heq; simp [Flat.step?] at hstep",
 "intro msg heq; subst heq; rw [Flat_step?_assign_error sf name _ hfnv msg sa hm] at hstep; simp at hstep",
 "intro msg heq; subst heq; simp_all [Flat.step?]",
 "intro msg heq; cases heq"]
```

The exact tactic depends on context. The key is: substitute `t = .error msg`, apply the `_error` theorem for the parent expression form, then show `hstep` becomes contradictory.

**IMPORTANT**: Each sorry is inside a different expression form (assign, if, unary, binary, etc.). The `_error` theorem name changes:
- L3344 (assign): `Flat_step?_assign_error`
- L3463 (if): look for `Flat_step?_if_error`
- L3671 (binary): look for `Flat_step?_binary_lhs_error` or `_rhs_error`
- etc.

### Your targets (TOP half only — wasmspec does bottom):
L3237, L3344, L3463, L3562, L3671, L3767, L3826, L3898, L4108, L4291, L4358, L4567

### Workflow
1. `lean_goal` at the sorry line to see context
2. Identify the parent expression form (assign, if, binary, etc.)
3. Find the matching `_error` theorem with `lean_local_search`
4. `lean_multi_attempt` with substitution + error theorem approach
5. If it works, edit the file to replace sorry
6. Build after every 3-4 closures

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw) — PRIMARY TARGET
- DO NOT edit ANFConvertCorrect.lean
- LOG to agents/jsspec/log.md

## TARGET: Close at least 6 hnoerr sorries → CC from 44 to ≤38
