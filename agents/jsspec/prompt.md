# jsspec — DELETE 47 dead-code theorems + close real CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## GREAT WORK on Fix D revert! Now clean up.

Your 18:00 run reverted Fix D and eliminated 22 hnoerr sorries. Excellent.
But there are still 47 dead-code "Fix D reverted" error theorems with sorry bodies.
These are NEVER CALLED. Delete them to drop grep count from 69 → 22.

## PRIORITY 1: DELETE ALL "Fix D reverted" dead-code sorries (instant -47)

Search for all lines containing `sorry -- Fix D reverted` in ClosureConvertCorrect.lean.
These are error companion theorems that are no longer referenced after the Fix D revert.
DELETE each entire theorem (not just the sorry line — delete the full theorem including
its signature and any doc comment).

Approximate line ranges (verify before deleting):
- L1627-2157: bulk of Fix D reverted sorries
- L2289-2606: remaining Fix D reverted sorries

**Verification**: After deletion, search for any references to the deleted theorem names.
If any are still referenced, keep those. Delete only truly unreferenced ones.

Build after deletion. grep -c sorry should drop from 69 to ~22.

## PRIORITY 2: Close real sorries (20 remaining after cleanup)

After deleting dead code, these are the real sorries to close:

### EASIEST (start here):
- **L4902**: ExprAddrWF objectLit — `lean_goal`, try `cases hexprwf; assumption` or `simp [ExprAddrWF]`
- **L5000**: ExprAddrWF arrayLit — same approach
- **L2960**: small sorry — `lean_goal` to understand

### MEDIUM:
- **L3279**: CCState threading (1 sorry) — `lean_goal`, try omega/simp
- **L3301**: CCState threading (2 sorries) — same approach
- **L4949**: CCState threading: convertPropList concatenation
- **L5251**: CCState threading: while_ lowering

### HARDER (skip if stuck):
- **L2766, L2876**: convertExpr_not_lit — need to prove convertExpr ≠ .lit for stub constructors
- **L3795**: callee is value (arg stepping or call execution)
- **L3796**: newObj — similar to call
- **L4364**: getIndex string semantic mismatch — MAY BE UNPROVABLE
- **L4536, L4858, L4956**: value sub-cases (heap reasoning)
- **L5130**: functionDef
- **L5220**: tryCatch

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf sorries (L1369-1370) — unprovable stubs

## WORKFLOW:
1. Delete dead code FIRST (Priority 1). Build. Verify count.
2. Then start with EASIEST sorry. `lean_goal` → `lean_multi_attempt` → move on if stuck after 10 min.
3. Log each sorry attempted and result.

## TARGET: Delete 47 dead-code + close at least 2 real sorries → CC from 69 to ~20
