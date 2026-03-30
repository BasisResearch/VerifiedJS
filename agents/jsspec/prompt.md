# jsspec — DELETE 22 dead-code "Fix D reverted" sorries + close real CC sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## STATE (22:05): CC has 41 grep-sorry, 15 real sorries

### Sorry breakdown:
- **22 dead-code** "Fix D reverted" (L1760-2495): DELETE THESE
- **2 unprovable stubs** (L1502-1503 forIn/forOf): DO NOT TOUCH
- **15 real sorries**: see list below
- **2 comment-only lines** with "sorry" (L540, L2804): not actual sorry

## PRIORITY 1: DELETE ALL 22 "Fix D reverted" dead-code theorems

Search: `grep -n "Fix D reverted" VerifiedJS/Proofs/ClosureConvertCorrect.lean`

These are error companion theorems that are NEVER CALLED after the Fix D revert.
For each one, delete the ENTIRE theorem (signature, doc comment, and sorry body).
Lines: L1760, 1778, 1796, 1814, 1858, 1876, 1894, 1912, 1930, 1948, 1966, 1984,
2003, 2035, 2053, 2105, 2123, 2422, 2436, 2470, 2480, 2495.

**Verification**: After deletion, grep for each deleted theorem name. If still referenced, keep it.

Build after deletion. `grep -c sorry` should drop from 41 to ~19.

## PRIORITY 2: Close real sorries (15 remaining after cleanup)

### EASIEST — do these first:
- **L2857**: standalone sorry — `lean_goal`, try `simp_all` / `omega` / `exact`
- **L3176**: CCState threading (if/else conversion) — `lean_goal`, likely needs `omega` or explicit Nat arithmetic
- **L3198**: 2 sorries (CCState threading) — same approach

### MEDIUM:
- **L2663**: needs `convertExpr_not_lit` for 3 stub constructors
- **L2773**: same class as L2663
- **L5237**: CCState threading: while_ lowering

### HARDER (skip if stuck >10 min each):
- **L3692**: callee is value (arg stepping / call execution)
- **L3693**: newObj
- **L4261**: getIndex string semantic mismatch — MAY BE UNPROVABLE
- **L4433**: value sub-case (heap reasoning)
- **L4755**: all props values: heap allocation
- **L4938**: all elements values: heap allocation
- **L5116**: functionDef
- **L5206**: tryCatch

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf sorries (L1502-1503) — unprovable stubs
- Value sub-cases (L3692, L4433, L4755, L4938) — wasmspec working on these

## TARGET: Delete 22 dead-code + close at least 3 real sorries → CC from 41 to ~14
