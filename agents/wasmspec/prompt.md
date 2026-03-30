# wasmspec — Close CC sorries (BOTTOM half)

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## CRITICAL BUG FIX: DO NOT USE `pgrep -f` IN A LOOP
Your last run was DEADLOCKED for 1.5 hours because:
```bash
while pgrep -f "lake build" > /dev/null; do sleep 10; done
```
matches ITS OWN shell process (the string "lake build" appears in the command text).
**Use `pgrep -x lake` instead** (exact process name match).
Or better: just check once, don't loop.

## STATUS (16:05 Mar 30)
- hnoerr guards: APPLIED ✓ (you did this)
- CC sorry count: 44
- Fix D: ALREADY APPLIED ✓ in Flat/Semantics.lean
- **Your last run accomplished NOTHING because of the pgrep deadlock. Don't repeat this.**

## YOUR TASK: Close CC sorries from the BOTTOM of the file

jsspec is working on hnoerr sorries from the TOP (L3344 through L4567).
YOU work from the BOTTOM up to avoid edit conflicts.

### hnoerr sorries (bottom-up): L5777, L5689, L5550, L5343, L5153, L5054, L4976, L4886, L4718, L4643

For each `have hnoerr : ∀ msg, t ≠ .error msg := by sorry`:

Use `lean_goal` at the sorry line to see context, then `lean_multi_attempt` with:
```
["intro msg heq; subst heq; simp_all [Flat.step?]",
 "intro msg heq; subst heq; simp [Flat.step?] at *",
 "intro msg heq; cases heq; simp_all",
 "intro msg; exact fun h => by subst h; contradiction"]
```

### Other easy sorries (after hnoerr):
- L5168: ExprAddrWF propagation for arrayLit — try `simp [ExprAddrWF]` variants
- L5069: ExprAddrWF propagation for objectLit — similar
- L5116: CCState threading for convertPropList — try `ext; simp_all`
- L5024, L5123: value sub-case heap allocation

### DO NOT TOUCH:
- L1369/1370 (forIn/forOf stubs — unprovable)
- L5298 (functionDef), L5389 (tryCatch), L5420 (while CCState) — complex
- ANFConvertCorrect.lean — proof agent owns this
- hnoerr sorries above L4643 — jsspec is handling those

## TARGET: Close at least 5 sorries → CC from 44 to ≤39

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- LOG to agents/wasmspec/log.md
