# jsspec — Close CC hnoerr sorries (Fix D is DONE)

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- Check builds with: `pgrep -x lake` (not `-f`)

## STATUS (16:05 Mar 30)
- **Fix D: ALREADY APPLIED** ✓ (91 `.error msg` patterns in Flat/Semantics.lean)
- **hnoerr guards: APPLIED** ✓ (97 occurrences in CC)
- **DO NOT apply Fix D again — it is DONE.**
- CC: 44 sorries. 20 are `hnoerr` sorries. These are MECHANICAL.

## YOUR TASK: Close hnoerr sorries in ClosureConvertCorrect.lean (TOP HALF)

There are 20 instances of this pattern:
```lean
have hnoerr : ∀ msg, t ≠ .error msg := by sorry
```

Each one appears inside a `| some (t, sa) =>` match arm where `t` came from `Flat.step?` on a sub-expression that is NOT an error (because with Fix D, error sub-steps are caught by a prior match arm).

### Proof strategy for each hnoerr sorry:

With Fix D, `Flat.step?` on a compound expression matches `.error msg` FIRST and produces `.lit .undefined`. If we're in the `| some (t, sa) =>` arm (not the error arm), then `t ≠ .error msg`.

Try these tactics at each sorry (use `lean_multi_attempt`):
```
["intro msg heq; subst heq; simp_all [Flat.step?]",
 "intro msg heq; subst heq; simp [Flat.step?] at *",
 "intro msg heq; cases heq; simp_all",
 "intro msg; exact fun h => by subst h; contradiction",
 "intro msg heq; subst heq; exact absurd hstep rfl"]
```

### Target sorries (TOP half — you handle these):
L3344, L3463, L3671, L3767, L3826, L3898, L4108, L4291, L4358, L4567

wasmspec handles BOTTOM half (L4643+) to avoid conflicts.

Start with L3344 (assign context — simplest). Use `lean_goal` at L3344 first to see exact context. Then try the tactics.

Build after every 3-4 closures.

### Also target: 2 hev_noerr sorries (L3237, L3562)
Same class but for expression evaluation events.

## SECONDARY: Stage convertExpr_not_lit lemma
If you finish hnoerr sorries, write to `.lake/_tmp_fix/convertExpr_not_lit.lean`:
```lean
theorem convertExpr_not_lit (e : Flat.Expr) (sc : CCState)
    (hne : ∀ v, e ≠ .lit v) :
    ∀ v, (Flat.convertExpr e sc).1 ≠ .lit v
```
This unblocks CC sorries at L2898, L3008.

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw) — PRIMARY TARGET
- DO NOT edit: `VerifiedJS/Flat/Semantics.lean` (Fix D done)
- DO NOT edit: `VerifiedJS/Proofs/ANFConvertCorrect.lean`
- LOG to agents/jsspec/log.md

## TARGET: Close at least 5 hnoerr sorries → CC from 44 to ≤39
